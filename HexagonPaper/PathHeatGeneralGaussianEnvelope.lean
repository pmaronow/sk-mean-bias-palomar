module
public import HexagonPaper.PathHeatEnvelope
public import FourPapersCommon.FiniteStateCascadeGrowth
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.MeasureTheory.Measure.Count

@[expose] public section

/-! The common reference envelope allows an arbitrary fixed Gaussian
auxiliary law, including noncentered, correlated and degenerate laws, and
an actual finite counting variable. No auxiliary spatial derivative is used. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon Paper
open scoped Topology BigOperators NNReal
namespace HexagonPaper
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {E J K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [Fintype J] [Fintype K] [MeasurableSpace K] [MeasurableSingletonClass K]

abbrev pathHeatGeneralBaseSample (E J K : Type*) := (E×(J→WienerPath))×K

def pathHeatGeneralCountMeasure (μ : Measure E) : Measure (pathHeatGeneralBaseSample E J K) :=
  (μ.prod (Measure.pi (fun _ : J=>canonicalWienerMeasure))).prod Measure.count

def pathHeatGeneralUniformMeasure [Nonempty K] (μ : Measure E) : Measure (pathHeatGeneralBaseSample E J K) :=
  (μ.prod (Measure.pi (fun _ : J=>canonicalWienerMeasure))).prod (PMF.uniformOfFintype K).toMeasure

instance pathHeatGeneralCountMeasure_finite (μ : Measure E) [IsGaussian μ] :
    IsFiniteMeasure (pathHeatGeneralCountMeasure (J:=J) (K:=K) μ) := by
  unfold pathHeatGeneralCountMeasure
  infer_instance

instance pathHeatGeneralUniformMeasure_probability [Nonempty K]
    (μ : Measure E) [IsGaussian μ] :
    IsProbabilityMeasure (pathHeatGeneralUniformMeasure (J:=J) (K:=K) μ) := by
  unfold pathHeatGeneralUniformMeasure
  infer_instance

def pathHeatGeneralRadius (ω : pathHeatGeneralBaseSample E J K) : ℝ :=
  ‖ω.1.1‖+∑j : J,‖ω.1.2 j‖

def pathHeatGeneralEnvelope (C : ℝ) (ω : pathHeatGeneralBaseSample E J K) : ℝ :=
  Real.exp (C*(1+pathHeatGeneralRadius ω))

theorem integrable_pathHeatGeneralEnvelope_count (μ : Measure E) [IsGaussian μ] (C : ℝ) :
    Integrable (pathHeatGeneralEnvelope (J:=J) (K:=K) C) (pathHeatGeneralCountMeasure μ) := by
  have hg := integrable_exp_mul_norm_gaussian μ C
  have hw : Integrable (fun w : J→WienerPath=>∏j : J,Real.exp (C*‖w j‖))
      (Measure.pi (fun _ : J=>canonicalWienerMeasure)) :=
    Integrable.fintype_prod (fun _=>integrable_exp_norm_canonicalWienerMeasure C)
  have hk : Integrable (fun _ : K=>(1:ℝ)) Measure.count := integrable_const _
  unfold pathHeatGeneralCountMeasure
  convert ((hg.mul_prod hw).const_mul (Real.exp C)).mul_prod hk using 1
  funext ω
  simp only [pathHeatGeneralEnvelope,pathHeatGeneralRadius,mul_one,←Real.exp_sum,Finset.mul_sum,←Real.exp_add]
  congr 1
  simp only [mul_add,mul_one,Finset.mul_sum]

theorem integrable_pathHeatGeneralEnvelope_uniform [Nonempty K]
    (μ : Measure E) [IsGaussian μ] (C : ℝ) :
    Integrable (pathHeatGeneralEnvelope (J:=J) (K:=K) C) (pathHeatGeneralUniformMeasure μ) := by
  have hg := integrable_exp_mul_norm_gaussian μ C
  have hw : Integrable (fun w : J→WienerPath=>∏j : J,Real.exp (C*‖w j‖))
      (Measure.pi (fun _ : J=>canonicalWienerMeasure)) :=
    Integrable.fintype_prod (fun _=>integrable_exp_norm_canonicalWienerMeasure C)
  have hk : Integrable (fun _ : K=>(1:ℝ)) (PMF.uniformOfFintype K).toMeasure := integrable_const _
  unfold pathHeatGeneralUniformMeasure
  convert ((hg.mul_prod hw).const_mul (Real.exp C)).mul_prod hk using 1
  funext ω
  simp only [pathHeatGeneralEnvelope,pathHeatGeneralRadius,mul_one,←Real.exp_sum,Finset.mul_sum,←Real.exp_add]
  congr 1
  simp only [mul_add,mul_one,Finset.mul_sum]

theorem pathHeatGeneral_linearGrowth_envelope
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (p : pathHeatGeneralBaseSample E J K→C(X,ℝ)) (ell : pathHeatGeneralBaseSample E J K→ℝ)
    (C R : ℝ) (hC : 0≤C) (hR : 0≤R)
    (hpath : ∀ω,‖p ω‖≤R*(∑j : J,‖ω.1.2 j‖))
    (hgrowth : ∀ω,|ell ω|≤C*(1+‖ω.1.1‖+‖p ω‖)) :
    ∀ω,Real.exp (ell ω)≤pathHeatGeneralEnvelope (C*(1+R)) ω := by
  intro ω
  apply Real.exp_le_exp.mpr
  have hsum : 0≤∑j : J,‖ω.1.2 j‖ := Finset.sum_nonneg (fun _ _=>norm_nonneg _)
  have haux := norm_nonneg ω.1.1
  have hp := hpath ω
  have hgrowth' := (le_abs_self (ell ω)).trans (hgrowth ω)
  change ell ω≤C*(1+R)*(1+(‖ω.1.1‖+∑j : J,‖ω.1.2 j‖))
  nlinarith [mul_nonneg hC hR,mul_nonneg hC hsum,mul_nonneg hC haux,
    mul_nonneg (mul_nonneg hC hR) haux]

theorem pathHeatGeneral_common_positive_normalizer [Nonempty K]
    (μ : Measure E) [IsGaussian μ] (C : ℝ) (ell : pathHeatGeneralBaseSample E J K→ℝ)
    (hm : Measurable ell) (hgrowth : ∀ω,|ell ω|≤C*(1+pathHeatGeneralRadius ω)) :
    0<(∫ω,pathHeatGeneralEnvelope (J:=J) (K:=K) (-C) ω∂pathHeatGeneralUniformMeasure μ) ∧
    (∫ω,pathHeatGeneralEnvelope (J:=J) (K:=K) (-C) ω∂pathHeatGeneralUniformMeasure μ)≤
      (∫ω,Real.exp (ell ω)∂pathHeatGeneralUniformMeasure μ) := by
  have hi := integrable_pathHeatGeneralEnvelope_uniform (J:=J) (K:=K) μ (-C)
  have hu := integrable_pathHeatGeneralEnvelope_uniform (J:=J) (K:=K) μ C
  have hw : Integrable (fun ω=>Real.exp (ell ω)) (pathHeatGeneralUniformMeasure μ) := by
    apply hu.mono' hm.exp.aestronglyMeasurable
    exact .of_forall fun ω=>by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hgrowth ω))
  refine ⟨integral_exp_pos hi,integral_mono hi hw (fun ω=>?_)⟩
  apply Real.exp_le_exp.mpr
  have hh := (abs_le.mp (hgrowth ω)).1
  simpa only [neg_mul] using hh

end HexagonPaper
