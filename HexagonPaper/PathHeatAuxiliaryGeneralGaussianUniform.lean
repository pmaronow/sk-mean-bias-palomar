module
public import HexagonPaper.PathHeatAuxiliaryGeneralGaussian

@[expose] public section

/-! Exponential-envelope integration for untouched auxiliary variables in
any complete separable normed Gaussian space, with actual finite counting
or uniform auxiliary law. No standard, centered or nonsingular reduction
is imposed on the Gaussian measure. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon
open scoped NNReal ENNReal Topology
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {E K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace K]

def pathHeatAuxiliaryNormEnvelope (C : ℝ) (ω : E × K) : ℝ :=
  Real.exp (C * (1 + ‖ω.1‖))

theorem integrable_pathHeatAuxiliaryNormEnvelope_prod
    (μ : Measure E) [IsGaussian μ] (κ : Measure K) [IsFiniteMeasure κ] (C : ℝ) :
    Integrable (pathHeatAuxiliaryNormEnvelope (E:=E) (K:=K) C) (μ.prod κ) := by
  have hg : Integrable (fun g : E => Real.exp C * Real.exp (C * ‖g‖)) μ :=
    (integrable_exp_mul_norm_gaussian μ C).const_mul (Real.exp C)
  have hk : Integrable (fun _ : K => (1 : ℝ)) κ := integrable_const _
  convert hg.mul_prod hk using 1
  funext ω
  simp only [pathHeatAuxiliaryNormEnvelope, mul_one, ← Real.exp_add]
  congr 1
  ring

theorem integrable_pathHeatAuxiliaryNormEnvelope_prod_power
    (μ : Measure E) [IsGaussian μ] (κ : Measure K) [IsFiniteMeasure κ]
    (C : ℝ) (p : ℕ) :
    Integrable (fun ω : E × K => (pathHeatAuxiliaryNormEnvelope C ω) ^ p) (μ.prod κ) := by
  convert integrable_pathHeatAuxiliaryNormEnvelope_prod μ κ ((p : ℝ) * C) using 1
  funext ω
  simp only [pathHeatAuxiliaryNormEnvelope, ← Real.exp_nat_mul]
  congr 1
  ring

theorem pathHeat_auxiliary_general_gaussian_raw_data
    (μ : Measure E) [IsGaussian μ] (κ : Measure K) [IsFiniteMeasure κ]
    (f d : ℝ → E × K → ℝ) (S : Set ℝ) (a Cf Cd R : ℝ)
    (hS : S ∈ 𝓝 a)
    (hfm : ∀ z ∈ S, AEStronglyMeasurable (f z) (μ.prod κ))
    (hdm : AEStronglyMeasurable (d a) (μ.prod κ))
    (hf : ∀ ω, ‖f a ω‖ ≤ Cf * pathHeatAuxiliaryNormEnvelope R ω)
    (hd : ∀ ω, ∀ z ∈ S, ‖d z ω‖ ≤ Cd * pathHeatAuxiliaryNormEnvelope R ω)
    (hderiv : ∀ ω, ∀ z ∈ S, HasDerivAt (fun u => f u ω) (d z ω) z) :
    PathHeatAuxiliaryRawData (μ.prod κ) f d S a
      (fun ω => Cd * pathHeatAuxiliaryNormEnvelope R ω) := by
  have hEi := integrable_pathHeatAuxiliaryNormEnvelope_prod μ κ R
  exact ⟨hfm,(hEi.const_mul Cf).mono' (hfm a (mem_of_mem_nhds hS)) (.of_forall hf),
    hdm,hd,hEi.const_mul Cd,hderiv⟩

theorem integrable_pathHeatAuxiliaryNormEnvelope_count [Fintype K]
    (μ : Measure E) [IsGaussian μ] (C : ℝ) :
    Integrable (pathHeatAuxiliaryNormEnvelope (E:=E) (K:=K) C)
      (μ.prod Measure.count) :=
  integrable_pathHeatAuxiliaryNormEnvelope_prod μ Measure.count C

theorem integrable_pathHeatAuxiliaryNormEnvelope_uniform [Fintype K] [Nonempty K]
    (μ : Measure E) [IsGaussian μ] (C : ℝ) :
    Integrable (pathHeatAuxiliaryNormEnvelope (E:=E) (K:=K) C)
      (μ.prod (PMF.uniformOfFintype K).toMeasure) :=
  integrable_pathHeatAuxiliaryNormEnvelope_prod μ _ C

theorem pathHeat_count_eq_card_smul_uniform [Fintype K] [Nonempty K]
    [MeasurableSingletonClass K] :
    (Measure.count : Measure K) =
      (Fintype.card K : ℝ≥0∞) • (PMF.uniformOfFintype K).toMeasure := by
  classical
  apply Measure.ext_of_singleton
  intro k
  rw [Measure.count_singleton, Measure.smul_apply,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton k),
    PMF.uniformOfFintype_apply, smul_eq_mul]
  have hc : (Fintype.card K : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  exact (ENNReal.mul_inv_cancel hc (by simp)).symm

theorem pathHeat_gaussian_count_eq_card_smul_uniform [Fintype K] [Nonempty K]
    [MeasurableSingletonClass K] (μ : Measure E) [IsGaussian μ] :
    μ.prod Measure.count =
      (Fintype.card K : ℝ≥0∞) • (μ.prod (PMF.uniformOfFintype K).toMeasure) := by
  rw [pathHeat_count_eq_card_smul_uniform, Measure.prod_smul_right]

end HexagonPaper
