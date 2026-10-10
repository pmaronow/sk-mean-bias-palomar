module
public import QuantitativeFollowup.AnisotropicNativeSpinConditionals
public import FourPapersCommon.PullbackIndicatorIntegral

@[expose] public section

/-! The actual terminal anisotropic Gibbs spin is attached to the native
full-profile diffusion by its genuine Markov kernel. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128

def anisotropicMeasureTerminalKernel (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) :
    Kernel (AnisotropicDisorderBrownianSample n) (Configuration n) :=
  (anisotropicTerminalSpinKernel D).comap (anisotropicProcessParameter D μ 1)
    ((adapted_anisotropicProcessParameter D μ 1).mono ((anisotropicBrownianFiltration n).le _) le_rfl)

instance anisotropicMeasureTerminalKernel_markov (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) : IsMarkovKernel (anisotropicMeasureTerminalKernel D μ) := by
  unfold anisotropicMeasureTerminalKernel
  infer_instance

def anisotropicMeasureSpinPathLaw (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a : ℝ) : Measure (AnisotropicDisorderBrownianSample n×Configuration n) :=
  (anisotropicMeasureSampleLaw D μ a) ⊗ₘ anisotropicMeasureTerminalKernel D μ

instance anisotropicMeasureSpinPathLaw_probability (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) : IsProbabilityMeasure (anisotropicMeasureSpinPathLaw D μ a) := by
  unfold anisotropicMeasureSpinPathLaw
  infer_instance

def anisotropicSpinPast (n : ℕ) (q : ℝ≥0) :
    MeasurableSpace (AnisotropicDisorderBrownianSample n×Configuration n) :=
  (anisotropicBrownianFiltration n q).comap Prod.fst

theorem anisotropicSpinPast_le (n : ℕ) (q : ℝ≥0) :
    anisotropicSpinPast n q≤(inferInstance : MeasurableSpace (AnisotropicDisorderBrownianSample n×Configuration n)) :=
  (MeasurableSpace.comap_mono ((anisotropicBrownianFiltration n).le q)).trans measurable_fst.comap_le

theorem anisotropicMeasureSpinPathLaw_fst (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) :
    (anisotropicMeasureSpinPathLaw D μ a).fst=anisotropicMeasureSampleLaw D μ a := by
  unfold anisotropicMeasureSpinPathLaw
  exact Measure.fst_compProd _ _

theorem measurePreserving_anisotropicMeasureSpinPathLaw_fst (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) :
    MeasurePreserving Prod.fst (anisotropicMeasureSpinPathLaw D μ a) (anisotropicMeasureSampleLaw D μ a) :=
  ⟨measurable_fst,anisotropicMeasureSpinPathLaw_fst D μ a⟩

theorem integral_anisotropicMeasureSpinPathLaw_sample (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (F : AnisotropicDisorderBrownianSample n→ℝ) (hF : Measurable F) :
    (∫p,F p.1 ∂anisotropicMeasureSpinPathLaw D μ a)=∫sample,F sample ∂anisotropicMeasureSampleLaw D μ a := by
  rw [←anisotropicMeasureSpinPathLaw_fst D μ a]
  exact (integral_map measurable_fst.aemeasurable hF.aestronglyMeasurable).symm

theorem integral_anisotropicMeasureSpinPathLaw_terminal_weight (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (Z : AnisotropicDisorderBrownianSample n→ℝ)
    (hZ : Measurable Z) (B : ℝ) (hB : ∀sample,‖Z sample‖≤B) (f : Configuration n→ℝ) :
    (∫p,Z p.1*f p.2 ∂anisotropicMeasureSpinPathLaw D μ a)=
      ∫sample,Z sample*anisotropicTerminalFeatureMean D f (anisotropicProcessParameter D μ 1 sample)
        ∂anisotropicMeasureSampleLaw D μ a := by
  let C : ℝ:=∑σ : Configuration n,‖f σ‖
  have hf (σ : Configuration n) : ‖f σ‖≤C :=
    Finset.single_le_sum (fun τ _=>norm_nonneg (f τ)) (Finset.mem_univ σ)
  have hm : Measurable (fun p : AnisotropicDisorderBrownianSample n×Configuration n=>Z p.1*f p.2) :=
    (hZ.comp measurable_fst).mul ((measurable_of_finite f).comp measurable_snd)
  have hB0 : 0≤B := (norm_nonneg (Z (0,0))).trans (hB (0,0))
  have hi : Integrable (fun p : AnisotropicDisorderBrownianSample n×Configuration n=>Z p.1*f p.2)
      (anisotropicMeasureSpinPathLaw D μ a) := by
    apply (integrable_const (B*C)).mono' hm.aestronglyMeasurable
    exact .of_forall fun p=>by
      rw [norm_mul]
      exact mul_le_mul (hB p.1) (hf p.2) (norm_nonneg _) hB0
  rw [anisotropicMeasureSpinPathLaw,Measure.integral_compProd hi]
  apply integral_congr_ae
  exact .of_forall fun sample=>by
    change (∫σ,Z sample*f σ ∂anisotropicTerminalSpinKernel D (anisotropicProcessParameter D μ 1 sample))=_
    rw [integral_const_mul]
    rfl

theorem anisotropicProcessSpinResponse_one (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (P : AnisotropicParameter n) (i : Fin n) :
    anisotropicMeasureTailMagnetization D μ 1 P i=anisotropicTerminalFeatureMean D (fun σ=>Paper.spinSign (σ i)) P := by
  have h := ((EuclideanSpace.proj i).continuous.tendsto _).comp
    ((tendstoUniformly_anisotropicFiniteDyadicTailMagnetization D μ).tendsto_at (1,P))
  change Tendsto (fun j=>anisotropicFiniteTailSpinResponse D
    (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) 1 P i) atTop
      (𝓝 (anisotropicMeasureTailMagnetization D μ 1 P i)) at h
  simp_rw [anisotropicFiniteTailSpinResponse_one] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

end QuantitativeFollowup
