module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseProfilePaths
public import QuantitativeFollowup.FollowupCavityRestTraceColumns

@[expose] public section

/-! Moving native rest covariance columns converge in the actual continuous
path norm. The literal scalar response then passes by its genuine uniform
operator bound and its already established weak-profile continuity. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped Topology NNReal
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 650000
set_option maxSynthPendingDepth 128

theorem tendsto_cavityRestOverlapMean_profile {I : Type*} {l : Filter I}
    [l.IsCountablyGenerated] (D : AnisotropicSpinModel n)
    {μ : I→Paper.ParisiMeasure} {ν : Paper.ParisiMeasure}
    (hμ : Tendsto μ l (𝓝 ν)) (a : ℝ) :
    Tendsto (fun j => cavityRestOverlapMean D (μ j) a) l
      (𝓝 (cavityRestOverlapMean D ν a)) := by
  exact tendsto_integral_anisotropicMeasureSampleLaw_profile_bounded D hμ a
    (fun j => cavityRestOverlapPath D (μ j)) (cavityRestOverlapPath D ν)
    (fun j => (measurable_cavityRestOverlapPath D (μ j)).aestronglyMeasurable)
    1 (by norm_num) (fun j => cavityRestOverlapPath_norm_le D (μ j))
    (.of_forall (tendsto_cavityRestOverlapPath_profile D hμ))

theorem tendsto_cavityRestCenteredOverlapPath_profile {I : Type*} {l : Filter I}
    [l.IsCountablyGenerated] (D : AnisotropicSpinModel n)
    {μ : I→Paper.ParisiMeasure} {ν : Paper.ParisiMeasure}
    (hμ : Tendsto μ l (𝓝 ν)) (a : ℝ)
    (ω : AnisotropicDisorderBrownianSample n) :
    Tendsto (fun j => cavityRestCenteredOverlapPath D (μ j) a ω) l
      (𝓝 (cavityRestCenteredOverlapPath D ν a ω)) :=
  (tendsto_cavityRestOverlapPath_profile D hμ ω).sub
    (tendsto_cavityRestOverlapMean_profile D hμ a)

theorem tendsto_cavityRestCovarianceColumn_profile {I : Type*} {l : Filter I}
    [l.IsCountablyGenerated] (D : AnisotropicSpinModel n)
    {μ : I→Paper.ParisiMeasure} {ν : Paper.ParisiMeasure}
    (hμ : Tendsto μ l (𝓝 ν)) (a : ℝ) {p : I→Paper.Overlap} {q : Paper.Overlap}
    (hp : Tendsto p l (𝓝 q)) :
    Tendsto (fun j => cavityRestCovarianceColumn D (μ j) a (p j)) l
      (𝓝 (cavityRestCovarianceColumn D ν a q)) := by
  let F := fun j ω => (cavityRestCenteredOverlapPath D (μ j) a ω (p j)) •
    cavityRestCenteredOverlapPath D (μ j) a ω
  have hm (j : I) : Measurable (F j) := by
    have hc := measurable_cavityRestCenteredOverlapPath D (μ j) a
    exact ((ContinuousMap.evalCLM ℝ (p j)).continuous.measurable.comp hc).smul hc
  have hb (j : I) (ω : AnisotropicDisorderBrownianSample n) : ‖F j ω‖≤1 := by
    rw [norm_smul]
    exact (mul_le_mul
      (((cavityRestCenteredOverlapPath D (μ j) a ω).norm_coe_le_norm (p j)).trans
        (cavityRestCenteredOverlapPath_norm_le D (μ j) a ω))
      (cavityRestCenteredOverlapPath_norm_le D (μ j) a ω)
      (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have ht (ω : AnisotropicDisorderBrownianSample n) :
      Tendsto (fun j => F j ω) l
        (𝓝 ((cavityRestCenteredOverlapPath D ν a ω q) •
          cavityRestCenteredOverlapPath D ν a ω)) := by
    have hc := tendsto_cavityRestCenteredOverlapPath_profile D hμ a ω
    exact (continuous_eval.tendsto _ |>.comp (hc.prodMk_nhds hp)).smul hc
  exact tendsto_integral_anisotropicMeasureSampleLaw_profile_bounded D hμ a F _
    (fun j => (hm j).aestronglyMeasurable) 1 (by norm_num) hb (.of_forall ht)

theorem tendsto_scalarResponseContinuousMap_profile_test {I : Type*} {l : Filter I}
    (β : ℝ) (hβ : β≠0) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    {μ : I→Paper.ParisiMeasure} {ν : Paper.ParisiMeasure}
    (hfloor : ∀j,μ j∈scalarFloor a) (hν : ν∈scalarFloor a)
    (hμ : Tendsto μ l (𝓝 ν)) {φ : I→C(Paper.Overlap,ℝ)} {ψ : C(Paper.Overlap,ℝ)}
    (hφ : Tendsto φ l (𝓝 ψ)) :
    Tendsto (fun j => scalarResponseContinuousMap β hβ a ha (φ j) ⟨μ j,hfloor j⟩) l
      (𝓝 (scalarResponseContinuousMap β hβ a ha ψ ⟨ν,hν⟩)) := by
  let J := fun j => cavityScalarContinuousResponse β hβ (μ j) a ha (hfloor j)
  have hm : Tendsto (fun j=>(⟨μ j,hfloor j⟩ : ScalarFloorMeasure a)) l
      (𝓝 (⟨ν,hν⟩ : ScalarFloorMeasure a)) := tendsto_subtype_rng.mpr hμ
  have hfixed := (continuous_scalarResponseContinuousMap β hβ a ha ψ).tendsto
    (⟨ν,hν⟩ : ScalarFloorMeasure a) |>.comp hm
  have herror : Tendsto (fun j => ‖J j (φ j)-J j ψ‖) l (𝓝 0) := by
    have ht : Tendsto (fun j => scalarResponseL2Bound β*‖φ j-ψ‖) l (𝓝 0) := by
      simpa only [sub_self,norm_zero,mul_zero] using
        ((hφ.sub_const ψ).norm).const_mul (scalarResponseL2Bound β)
    apply squeeze_zero (fun j => norm_nonneg _) _ ht
    intro j
    rw [←map_sub]
    exact cavityScalarContinuousResponse_norm_le β hβ (μ j) a ha (hfloor j) (φ j-ψ)
  have hzero : Tendsto (fun j => J j (φ j)-J j ψ) l (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [sub_zero] using herror)
  have ht := hzero.add hfixed
  have he (j : I) (η : C(Paper.Overlap,ℝ)) :
      J j η=scalarResponseContinuousMap β hβ a ha η ⟨μ j,hfloor j⟩ := by
    ext p
    rfl
  simp_rw [he] at ht
  simpa only [Function.comp_def,zero_add,sub_add_cancel] using ht

theorem tendsto_scalarResponseOperator_profile_covariance {I : Type*} {l : Filter I}
    [l.IsCountablyGenerated] (D : AnisotropicSpinModel n)
    (β : ℝ) (hβ : β≠0) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    {μ : I→Paper.ParisiMeasure} {ν : Paper.ParisiMeasure}
    (hfloor : ∀j,μ j∈scalarFloor a) (hν : ν∈scalarFloor a)
    (hμ : Tendsto μ l (𝓝 ν)) {p : I→Paper.Overlap} {q : Paper.Overlap}
    (hp : Tendsto p l (𝓝 q)) :
    Tendsto (fun j => scalarResponseOperator β hβ (μ j) a
      (cavityRestCovarianceColumn D (μ j) a (p j)) (p j)) l
      (𝓝 (scalarResponseOperator β hβ ν a (cavityRestCovarianceColumn D ν a q) q)) := by
  have ht := tendsto_scalarResponseContinuousMap_profile_test β hβ a ha hfloor hν hμ
    (tendsto_cavityRestCovarianceColumn_profile D hμ a hp)
  exact continuous_eval.tendsto _ |>.comp (ht.prodMk_nhds hp)

end QuantitativeFollowup
