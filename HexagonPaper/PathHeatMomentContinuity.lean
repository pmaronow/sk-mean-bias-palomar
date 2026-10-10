module
public import HexagonPaper.PathHeatNormalizedLimit

@[expose] public section

/-! Continuity of the actual normalized moments and centered response,
derived from a common integrable envelope and pointwise continuity. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace HexagonPaper
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {Z Ω : Type*} [TopologicalSpace Z] [FirstCountableTopology Z]
  [MeasurableSpace Ω] {μ : Measure Ω}

theorem continuous_pathHeat_weighted_integral
    (W G : Z→Ω→ℝ) (e : Ω→ℝ) (A : ℝ) (he : Integrable e μ)
    (hWm : ∀z,AEStronglyMeasurable (W z) μ) (hGm : ∀z,AEStronglyMeasurable (G z) μ)
    (hWp : ∀z,∀ᵐω ∂μ,0<W z ω) (hWe : ∀z,∀ᵐω ∂μ,W z ω≤e ω)
    (hG : ∀z,∀ᵐω ∂μ,|G z ω|≤A)
    (hWc : ∀ᵐω ∂μ,Continuous (fun z=>W z ω)) (hGc : ∀ᵐω ∂μ,Continuous (fun z=>G z ω)) :
    Continuous (fun z=>∫ω,W z ω*G z ω∂μ) := by
  refine continuous_of_dominated (fun z=>(hWm z).mul (hGm z)) ?_ (he.mul_const A) ?_
  · intro z
    filter_upwards [hWp z,hWe z,hG z] with ω hp hb hg
    rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos hp]
    exact mul_le_mul hb hg (abs_nonneg _) (hp.le.trans hb)
  · filter_upwards [hWc,hGc] with ω hw hg
    exact hw.mul hg

theorem continuous_pathHeat_normalized_moments [IsProbabilityMeasure μ] [Nonempty Z]
    (W F H J : Z→Ω→ℝ) (e : Ω→ℝ) (B C D : ℝ)
    (h : ∀z,PathHeatDominatedData μ (W z) (F z) (H z) (J z) e B C D)
    (hW : ∀ᵐω ∂μ,Continuous (fun z=>W z ω)) (hF : ∀ᵐω ∂μ,Continuous (fun z=>F z ω))
    (hH : ∀ᵐω ∂μ,Continuous (fun z=>H z ω)) (hJ : ∀ᵐω ∂μ,Continuous (fun z=>J z ω)) :
    Continuous (fun z=>pathHeatNormalizer μ (W z)) ∧
    Continuous (fun z=>pathHeatExpectation μ (W z) (F z)) ∧
    Continuous (fun z=>pathHeatResponse μ (W z) (F z) (H z) (J z)) := by
  let z₀ : Z := Classical.arbitrary Z
  have hZ : Continuous (fun z=>pathHeatNormalizer μ (W z)) := by
    refine continuous_of_dominated (fun z=>(h z).weight_measurable) ?_
      (h z₀).integrable_envelope ?_
    · intro z
      filter_upwards [(h z).weight_positive,(h z).weight_bound] with ω hp hb
      simpa only [Real.norm_eq_abs,abs_of_pos hp] using hb
    · exact hW
  have hp (z : Z) := (pathHeat_normalizer_positive (h z)).ne'
  have hIF : Continuous (fun z=>∫ω,W z ω*F z ω∂μ) := by
    exact continuous_pathHeat_weighted_integral W F e B (h z₀).integrable_envelope
      (fun z=>(h z).weight_measurable) (fun z=>(h z).observable_measurable)
      (fun z=>(h z).weight_positive) (fun z=>(h z).weight_bound)
      (fun z=>(h z).observable_bound) hW hF
  have hIH : Continuous (fun z=>∫ω,W z ω*H z ω∂μ) := by
    exact continuous_pathHeat_weighted_integral W H e C (h z₀).integrable_envelope
      (fun z=>(h z).weight_measurable) (fun z=>(h z).density_generator_measurable)
      (fun z=>(h z).weight_positive) (fun z=>(h z).weight_bound)
      (fun z=>(h z).density_generator_bound) hW hH
  have hIJ : Continuous (fun z=>∫ω,W z ω*J z ω∂μ) := by
    exact continuous_pathHeat_weighted_integral W J e D (h z₀).integrable_envelope
      (fun z=>(h z).weight_measurable) (fun z=>(h z).observable_generator_measurable)
      (fun z=>(h z).weight_positive) (fun z=>(h z).weight_bound)
      (fun z=>(h z).observable_generator_bound) hW hJ
  have hIFH : Continuous (fun z=>∫ω,W z ω*(F z ω*H z ω)∂μ) := by
    apply continuous_pathHeat_weighted_integral W (fun z ω=>F z ω*H z ω) e (B*C)
      (h z₀).integrable_envelope (fun z=>(h z).weight_measurable)
      (fun z=>(h z).observable_measurable.mul (h z).density_generator_measurable)
      (fun z=>(h z).weight_positive) (fun z=>(h z).weight_bound)
    · intro z
      filter_upwards [(h z).observable_bound,(h z).density_generator_bound] with ω hf hh
      rw [abs_mul]
      exact mul_le_mul hf hh (abs_nonneg _) (h z).nonneg_B
    · exact hW
    · filter_upwards [hF,hH] with ω hf hh
      exact hf.mul hh
  have hE : Continuous (fun z=>pathHeatExpectation μ (W z) (F z)) := hIF.div hZ hp
  refine ⟨hZ,hE,?_⟩
  have hr : (fun z=>pathHeatResponse μ (W z) (F z) (H z) (J z))=
      fun z=>(∫ω,W z ω*J z ω∂μ)/pathHeatNormalizer μ (W z)+
        (∫ω,W z ω*(F z ω*H z ω)∂μ)/pathHeatNormalizer μ (W z)-
        pathHeatExpectation μ (W z) (F z)*((∫ω,W z ω*H z ω∂μ)/pathHeatNormalizer μ (W z)) :=
    funext (fun z=>pathHeat_response_eq_raw (h z))
  rw [hr]
  exact ((hIJ.div hZ hp).add (hIFH.div hZ hp)).sub (hE.mul (hIH.div hZ hp))

theorem continuous_pathHeat_density_expectation [IsProbabilityMeasure μ] [Nonempty Z]
    (W F H J : Z→Ω→ℝ) (e : Ω→ℝ) (B C D : ℝ)
    (h : ∀z,PathHeatDominatedData μ (W z) (F z) (H z) (J z) e B C D)
    (hW : ∀ᵐω ∂μ,Continuous (fun z=>W z ω)) (hH : ∀ᵐω ∂μ,Continuous (fun z=>H z ω)) :
    Continuous (fun z=>pathHeatExpectation μ (W z) (H z)) := by
  let z₀ : Z := Classical.arbitrary Z
  have hZ : Continuous (fun z=>pathHeatNormalizer μ (W z)) := by
    refine continuous_of_dominated (fun z=>(h z).weight_measurable) ?_ (h z₀).integrable_envelope hW
    intro z
    filter_upwards [(h z).weight_positive,(h z).weight_bound] with ω hp hb
    simpa only [Real.norm_eq_abs,abs_of_pos hp] using hb
  have hIH := continuous_pathHeat_weighted_integral W H e C (h z₀).integrable_envelope
    (fun z=>(h z).weight_measurable) (fun z=>(h z).density_generator_measurable)
    (fun z=>(h z).weight_positive) (fun z=>(h z).weight_bound)
    (fun z=>(h z).density_generator_bound) hW hH
  exact hIH.div hZ (fun z=>(pathHeat_normalizer_positive (h z)).ne')

end HexagonPaper
