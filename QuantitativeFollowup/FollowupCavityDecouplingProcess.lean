module
public import QuantitativeFollowup.FollowupCavityDecouplingScalarState
public import QuantitativeFollowup.FollowupCavityDecouplingDriverLaw
public import FRSB.ConstantMassLaw

@[expose] public section

/-! Literal magnetization separation and joint whole-process law at zero
incident coupling. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

def cavityScalarMagnetization (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (q : Paper.Overlap) (W : Paper.BrownianSample) : ℝ:=
  Paper.parisiGradient β μ (q,Paper.selectedParisiItoState β 0 hβ μ (q:ℝ).toNNReal W)

theorem measurable_cavityScalarMagnetization (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (q : Paper.Overlap) : Measurable (cavityScalarMagnetization β hβ μ q) :=
  (Paper.continuous_parisiGradient β μ).measurable.comp
    (measurable_const.prodMk (FRSB.measurable_selectedParisiState_time β 0 hβ μ _))

theorem cavityScalarMagnetization_norm_le (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (q : Paper.Overlap) (W : Paper.BrownianSample) : ‖cavityScalarMagnetization β hβ μ q W‖≤1 :=
  Paper.norm_parisiGradient_le_one β μ _

theorem cavityRestProcessMagnetization_zero (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (q : Paper.Overlap)
    (p : AnisotropicDisorderBrownianSample (n+1)) :
    cavityRestFieldProjection n (anisotropicProcessMagnetization
      (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩) μ q p)=
      anisotropicProcessMagnetization (followupCavityRestSpinModel n β ρ hβ hρ) μ q
        (cavityRestSampleProjection n p) := by
  unfold anisotropicProcessMagnetization anisotropicProcessParameter
  rw [anisotropicDisorderInjection_apply,←anisotropicParameterPoint_field,
    followupCavityMeasureGradient_rest_zero,cavityRestMeasureState_zero μ n β ρ hβ hρ q q.property p]
  rw [anisotropicParameterPoint_field]
  rfl

theorem cavityLastProcessMagnetization_zero (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (q : Paper.Overlap)
    (p : AnisotropicDisorderBrownianSample (n+1)) :
    anisotropicProcessMagnetization
      (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩) μ q p (Fin.last n)=
      cavityScalarMagnetization (followupCavityScalarBeta n β ρ)
        (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' μ q (p.2 (Fin.last n)) := by
  unfold anisotropicProcessMagnetization anisotropicProcessParameter cavityScalarMagnetization
  rw [anisotropicDisorderInjection_apply,←anisotropicParameterPoint_field,
    followupCavityMeasureGradient_last_zero,cavityLastMeasureState_zero μ n β ρ hβ hρ q q.property p,
    Paper.selectedParisiItoState_eq _ _ _ _ (by simpa using Real.toNNReal_le_toNNReal q.property.2)]
  rw [Real.coe_toNNReal _ q.property.1]

def cavityRestMagnetizationCurve (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (p : AnisotropicDisorderBrownianSample n) : Paper.Overlap → QuantitativePaper.Field n :=
  fun q=>anisotropicProcessMagnetization (followupCavityRestSpinModel n β ρ hβ hρ) μ q p

def cavityScalarMagnetizationCurve (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (W : Paper.BrownianSample) : Paper.Overlap → ℝ :=
  fun q=>cavityScalarMagnetization (followupCavityScalarBeta n β ρ)
    (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' μ q W

def cavityZeroMagnetizationCurves (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (p : AnisotropicDisorderBrownianSample (n+1)) :
    (Paper.Overlap → QuantitativePaper.Field n) × (Paper.Overlap → ℝ) :=
  (fun q=>cavityRestFieldProjection n (anisotropicProcessMagnetization
    (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩) μ q p),
    fun q=>anisotropicProcessMagnetization
      (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩) μ q p (Fin.last n))

theorem measurable_cavityRestMagnetizationCurve (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) :
    Measurable (cavityRestMagnetizationCurve μ n β ρ hβ hρ) := by
  apply Measurable.of_eval
  intro q
  have hmap : Measurable (fun p : AnisotropicDisorderBrownianSample n=>(q,p)) :=
    measurable_const.prodMk measurable_id
  have hm := (measurable_uncurry_anisotropicProcessMagnetization
    (followupCavityRestSpinModel n β ρ hβ hρ) μ).comp hmap
  exact hm

theorem measurable_cavityScalarMagnetizationCurve (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) :
    Measurable (cavityScalarMagnetizationCurve μ n β ρ hβ hρ) :=
  Measurable.of_eval fun q=>measurable_cavityScalarMagnetization _ _ μ q

theorem cavityZeroMagnetizationCurves_eq (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) :
    cavityZeroMagnetizationCurves μ n β ρ hβ hρ =
      Prod.map (cavityRestMagnetizationCurve μ n β ρ hβ hρ)
        (cavityScalarMagnetizationCurve μ n β ρ hβ hρ) ∘ cavityZeroSampleSplit n := by
  funext p
  apply Prod.ext
  · funext q
    exact cavityRestProcessMagnetization_zero μ n β ρ hβ hρ q p
  · funext q
    exact cavityLastProcessMagnetization_zero μ n β ρ hβ hρ q p

theorem cavityZeroMagnetizationProcess_law (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ) :
    (anisotropicMeasureSampleLaw (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩) μ a).map
      (cavityZeroMagnetizationCurves μ n β ρ hβ hρ)=
      ((anisotropicMeasureSampleLaw (followupCavityRestSpinModel n β ρ hβ hρ) μ a).map
        (cavityRestMagnetizationCurve μ n β ρ hβ hρ)).prod
      (Paper.canonicalBrownianMeasure.map (cavityScalarMagnetizationCurve μ n β ρ hβ hρ)) := by
  have hf := measurable_cavityRestMagnetizationCurve μ n β ρ hβ hρ
  have hg := measurable_cavityScalarMagnetizationCurve μ n β ρ hβ hρ
  rw [Measure.map_prod_map _ _ hf hg,←cavityZeroSampleSplit_law μ n β ρ hβ hρ a,
    Measure.map_map (hf.prodMap hg) (measurable_cavityZeroSampleSplit n),
    cavityZeroMagnetizationCurves_eq]

end QuantitativeFollowup
