module
public import HexagonPaper.PathHeatAuxiliaryGaussianCount
public import FourPapersCommon.FiniteStateCascadeGrowth

@[expose] public section

/-! Untouched auxiliary variables may have any genuine Gaussian law,
including nonzero mean, correlated coordinates and degenerate covariance. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology
namespace HexagonPaper
open QuantitativePaper FourPapersCommon
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {h : ℕ} {K : Type*} [Fintype K] [MeasurableSpace K]

def pathHeatAuxiliaryGaussianCountMeasure (μ : Measure (QuantitativePaper.Field h)) :
    Measure (pathHeatAuxiliarySample h K) := μ.prod Measure.count

instance pathHeatAuxiliaryGaussianCountMeasure_finite
    (μ : Measure (QuantitativePaper.Field h)) [IsGaussian μ] :
    IsFiniteMeasure (pathHeatAuxiliaryGaussianCountMeasure (K:=K) μ) := by
  unfold pathHeatAuxiliaryGaussianCountMeasure
  infer_instance

theorem integrable_pathHeatAuxiliaryEnvelope_gaussian_count
    (μ : Measure (QuantitativePaper.Field h)) [IsGaussian μ] (C : ℝ) :
    Integrable (pathHeatAuxiliaryEnvelope (h:=h) (K:=K) C)
      (pathHeatAuxiliaryGaussianCountMeasure μ) := by
  have hg : Integrable (fun g : QuantitativePaper.Field h=>Real.exp C*Real.exp (C*‖g‖)) μ :=
    (integrable_exp_mul_norm_gaussian μ C).const_mul (Real.exp C)
  have hk : Integrable (fun _ : K=>(1 : ℝ)) Measure.count := integrable_const _
  unfold pathHeatAuxiliaryGaussianCountMeasure
  convert hg.mul_prod hk using 1
  funext ω
  simp only [pathHeatAuxiliaryEnvelope,mul_one,←Real.exp_add]
  congr 1
  ring

theorem integrable_pathHeatAuxiliaryEnvelope_gaussian_count_power
    (μ : Measure (QuantitativePaper.Field h)) [IsGaussian μ] (C : ℝ) (p : ℕ) :
    Integrable (fun ω : pathHeatAuxiliarySample h K=>(pathHeatAuxiliaryEnvelope C ω)^p)
      (pathHeatAuxiliaryGaussianCountMeasure μ) := by
  convert integrable_pathHeatAuxiliaryEnvelope_gaussian_count (K:=K) μ ((p : ℝ)*C) using 1
  funext ω
  simp only [pathHeatAuxiliaryEnvelope,←Real.exp_nat_mul]
  congr 1
  ring

theorem pathHeat_auxiliary_gaussian_count_raw_data
    (μ : Measure (QuantitativePaper.Field h)) [IsGaussian μ]
    (f d : ℝ→pathHeatAuxiliarySample h K→ℝ) (S : Set ℝ) (a Cf Cd R : ℝ)
    (hS : S∈𝓝 a)
    (hfm : ∀z∈S,AEStronglyMeasurable (f z) (pathHeatAuxiliaryGaussianCountMeasure μ))
    (hdm : AEStronglyMeasurable (d a) (pathHeatAuxiliaryGaussianCountMeasure μ))
    (hf : ∀ω,‖f a ω‖≤Cf*pathHeatAuxiliaryEnvelope R ω)
    (hd : ∀ω,∀z∈S,‖d z ω‖≤Cd*pathHeatAuxiliaryEnvelope R ω)
    (hderiv : ∀ω,∀z∈S,HasDerivAt (fun u=>f u ω) (d z ω) z) :
    PathHeatAuxiliaryRawData (pathHeatAuxiliaryGaussianCountMeasure μ) f d S a
      (fun ω=>Cd*pathHeatAuxiliaryEnvelope R ω) := by
  have hEi := integrable_pathHeatAuxiliaryEnvelope_gaussian_count (K:=K) μ R
  exact ⟨hfm,(hEi.const_mul Cf).mono' (hfm a (mem_of_mem_nhds hS)) (.of_forall hf),
    hdm,hd,hEi.const_mul Cd,hderiv⟩

end HexagonPaper
