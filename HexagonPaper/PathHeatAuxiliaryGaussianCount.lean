module
public import HexagonPaper.PathHeatAuxiliaryDifferentiation
public import QuantitativePaper.VectorTerminal
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.MeasureTheory.Measure.Count

@[expose] public section

/-! True auxiliary Gaussian and finite-count reference laws and their
common exponential envelopes. The counting measure is retained before
normalization; a uniform probability version is also available. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators Topology
namespace HexagonPaper
open QuantitativePaper
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {h : ℕ} {K : Type*} [Fintype K] [MeasurableSpace K] [MeasurableSingletonClass K]

abbrev pathHeatAuxiliarySample (h : ℕ) (K : Type*) := QuantitativePaper.Field h × K

def pathHeatAuxiliaryCountMeasure (h : ℕ) (K : Type*) [Fintype K]
    [MeasurableSpace K] : Measure (pathHeatAuxiliarySample h K) :=
  (fieldGaussian h).prod Measure.count

instance pathHeatAuxiliaryCountMeasure_finite :
    IsFiniteMeasure (pathHeatAuxiliaryCountMeasure h K) := by
  unfold pathHeatAuxiliaryCountMeasure
  infer_instance

def pathHeatAuxiliaryUniformMeasure (h : ℕ) (K : Type*) [Fintype K] [Nonempty K]
    [MeasurableSpace K] : Measure (pathHeatAuxiliarySample h K) :=
  (fieldGaussian h).prod (PMF.uniformOfFintype K).toMeasure

instance pathHeatAuxiliaryUniformMeasure_probability [Nonempty K] :
    IsProbabilityMeasure (pathHeatAuxiliaryUniformMeasure h K) := by
  unfold pathHeatAuxiliaryUniformMeasure
  infer_instance

def pathHeatAuxiliaryEnvelope (C : ℝ) (ω : pathHeatAuxiliarySample h K) : ℝ :=
  Real.exp (C*(1+‖ω.1‖))

theorem integrable_pathHeatAuxiliaryEnvelope_count (C : ℝ) :
    Integrable (pathHeatAuxiliaryEnvelope (h:=h) (K:=K) C)
      (pathHeatAuxiliaryCountMeasure h K) := by
  have hg : Integrable (fun g : QuantitativePaper.Field h=>Real.exp C*Real.exp (C*‖g‖))
      (fieldGaussian h) := (SYK.integrable_exp_mul_norm C).const_mul (Real.exp C)
  have hk : Integrable (fun _ : K=>(1 : ℝ)) Measure.count := integrable_const _
  unfold pathHeatAuxiliaryCountMeasure
  convert hg.mul_prod hk using 1
  funext ω
  simp only [pathHeatAuxiliaryEnvelope,mul_one,←Real.exp_add]
  congr 1
  ring

theorem integrable_pathHeatAuxiliaryEnvelope_uniform [Nonempty K] (C : ℝ) :
    Integrable (pathHeatAuxiliaryEnvelope (h:=h) (K:=K) C)
      (pathHeatAuxiliaryUniformMeasure h K) := by
  have hg : Integrable (fun g : QuantitativePaper.Field h=>Real.exp C*Real.exp (C*‖g‖))
      (fieldGaussian h) := (SYK.integrable_exp_mul_norm C).const_mul (Real.exp C)
  have hk : Integrable (fun _ : K=>(1 : ℝ)) (PMF.uniformOfFintype K).toMeasure := integrable_const _
  unfold pathHeatAuxiliaryUniformMeasure
  convert hg.mul_prod hk using 1
  funext ω
  simp only [pathHeatAuxiliaryEnvelope,mul_one,←Real.exp_add]
  congr 1
  ring

theorem integrable_pathHeatAuxiliaryEnvelope_count_power (C : ℝ) (p : ℕ) :
    Integrable (fun ω : pathHeatAuxiliarySample h K=>(pathHeatAuxiliaryEnvelope C ω)^p)
      (pathHeatAuxiliaryCountMeasure h K) := by
  convert integrable_pathHeatAuxiliaryEnvelope_count (h:=h) (K:=K) ((p : ℝ)*C) using 1
  funext ω
  simp only [pathHeatAuxiliaryEnvelope,←Real.exp_nat_mul]
  congr 1
  ring

theorem integrable_pathHeatAuxiliaryEnvelope_uniform_power [Nonempty K] (C : ℝ) (p : ℕ) :
    Integrable (fun ω : pathHeatAuxiliarySample h K=>(pathHeatAuxiliaryEnvelope C ω)^p)
      (pathHeatAuxiliaryUniformMeasure h K) := by
  convert integrable_pathHeatAuxiliaryEnvelope_uniform (h:=h) (K:=K) ((p : ℝ)*C) using 1
  funext ω
  simp only [pathHeatAuxiliaryEnvelope,←Real.exp_nat_mul]
  congr 1
  ring

/-- Integrating the actual finite Gaussian raw derivative leaves a single
common integrable envelope in the untouched auxiliary Gaussian variables. -/
theorem pathHeat_conditional_gaussian_raw_bound {n : ℕ}
    (ω : pathHeatAuxiliarySample h K) (f : QuantitativePaper.Field n→ℝ)
    (C R B : ℝ) (hC : 0≤C)
    (hf : Integrable f (fieldGaussian n))
    (hbound : ∀g,‖f g‖≤C*pathHeatAuxiliaryEnvelope R ω*Real.exp (B*‖g‖)) :
    ‖∫g,f g∂fieldGaussian n‖ ≤
      (C*(∫g : QuantitativePaper.Field n,Real.exp (B*‖g‖)∂fieldGaussian n))*
        pathHeatAuxiliaryEnvelope R ω := by
  have hg := (SYK.integrable_exp_mul_norm (ι:=Fin n) B).const_mul
    (C*pathHeatAuxiliaryEnvelope R ω)
  calc
    _ ≤ ∫g,‖f g‖∂fieldGaussian n := norm_integral_le_integral_norm _
    _ ≤ ∫g,C*pathHeatAuxiliaryEnvelope R ω*Real.exp (B*‖g‖)∂fieldGaussian n :=
      integral_mono hf.norm hg hbound
    _ = _ := by rw [integral_const_mul];ring

/-- Source linear growth and a uniformly bounded finite Price score give
the preceding raw derivative bound without any assumed Gaussian response. -/
theorem pathHeat_conditional_exp_score_bound {n : ℕ}
    (ω : pathHeatAuxiliarySample h K) (ell score : QuantitativePaper.Field n→ℝ)
    (C R B : ℝ) (hC : 0≤C)
    (hint : Integrable (fun g=>Real.exp (ell g)*score g) (fieldGaussian n))
    (hgrowth : ∀g,ell g≤R*(1+‖ω.1‖)+B*‖g‖)
    (hscore : ∀g,|score g|≤C) :
    ‖∫g,Real.exp (ell g)*score g∂fieldGaussian n‖ ≤
      (C*(∫g : QuantitativePaper.Field n,Real.exp (B*‖g‖)∂fieldGaussian n))*
        pathHeatAuxiliaryEnvelope R ω := by
  apply pathHeat_conditional_gaussian_raw_bound ω _ C R B hC hint
  intro g
  rw [norm_mul,Real.norm_eq_abs,Real.abs_exp,Real.norm_eq_abs]
  have he : Real.exp (ell g)≤pathHeatAuxiliaryEnvelope R ω*Real.exp (B*‖g‖) := by
    simpa only [pathHeatAuxiliaryEnvelope,Real.exp_add] using Real.exp_le_exp.mpr (hgrowth g)
  calc
    _ ≤ (pathHeatAuxiliaryEnvelope R ω*Real.exp (B*‖g‖))*C :=
      mul_le_mul he (hscore g) (abs_nonneg _) (by unfold pathHeatAuxiliaryEnvelope;positivity)
    _ = _ := by ring

/-- A genuine Gaussian/count envelope discharges all integrability fields
of the conditional finite Price integration receiver. -/
theorem pathHeat_auxiliary_count_raw_data
    (f d : ℝ→pathHeatAuxiliarySample h K→ℝ) (S : Set ℝ) (a Cf Cd R : ℝ)
    (hS : S∈𝓝 a)
    (hfm : ∀z∈S,AEStronglyMeasurable (f z) (pathHeatAuxiliaryCountMeasure h K))
    (hdm : AEStronglyMeasurable (d a) (pathHeatAuxiliaryCountMeasure h K))
    (hf : ∀ω,‖f a ω‖≤Cf*pathHeatAuxiliaryEnvelope R ω)
    (hd : ∀ω,∀z∈S,‖d z ω‖≤Cd*pathHeatAuxiliaryEnvelope R ω)
    (hderiv : ∀ω,∀z∈S,HasDerivAt (fun u=>f u ω) (d z ω) z) :
    PathHeatAuxiliaryRawData (pathHeatAuxiliaryCountMeasure h K) f d S a
      (fun ω=>Cd*pathHeatAuxiliaryEnvelope R ω) := by
  have hEi := integrable_pathHeatAuxiliaryEnvelope_count (h:=h) (K:=K) R
  exact ⟨hfm,(hEi.const_mul Cf).mono' (hfm a (mem_of_mem_nhds hS)) (.of_forall hf),
    hdm,hd,hEi.const_mul Cd,hderiv⟩

/-- The retained finite counting law has positive total mass. Positive
conditional normalizers therefore give a positive global normalizer. -/
theorem pathHeat_auxiliary_count_normalizer_pos [Nonempty K]
    (Z : pathHeatAuxiliarySample h K→ℝ)
    (hZi : Integrable Z (pathHeatAuxiliaryCountMeasure h K)) (hZ : ∀ω,0<Z ω) :
    0<(∫ω,Z ω∂pathHeatAuxiliaryCountMeasure h K) := by
  rw [integral_pos_iff_support_of_nonneg (fun ω=>(hZ ω).le) hZi]
  have hs : Function.support Z=univ := by ext ω;simp [Function.mem_support,(hZ ω).ne']
  rw [hs,pathHeatAuxiliaryCountMeasure,←univ_prod_univ,Measure.prod_prod]
  simp only [measure_univ,one_mul]
  exact pos_iff_ne_zero.mpr (Measure.count_ne_zero (Set.univ_nonempty : (Set.univ : Set K).Nonempty))

end HexagonPaper
