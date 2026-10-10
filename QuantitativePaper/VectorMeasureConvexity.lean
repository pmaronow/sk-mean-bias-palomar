module
public import QuantitativePaper.VectorMeasureMixConvexity
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.MeasureTheory.Measure.OpenPos

@[expose] public section

/-! Pointwise measure convexity of the genuine arbitrary-profile potential.
Bounded initial indicators first localize the control inequality; full support
of the concrete Gaussian disorder law then removes the null set. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem integral_vectorInitialFunction (f : Couplings n × ℝ → ℝ) :
    (∫sample,f sample.1 ∂vectorDisorderBrownianMeasure n) = ∫p,f p ∂completionLaw n := by
  have hh := integral_fun_fst (μ := completionLaw n) (ν := vectorBrownianMeasure n) f
  simpa only [vectorDisorderBrownianMeasure,probReal_univ,one_smul] using hh

theorem vectorMeasurePotential_mix_ae_le (μ ν : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t ≤ 1) (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) 1) :
    (fun p : Couplings n × ℝ => vectorMeasurePotential (Paper.parisiMix μ ν lam) β t p 0) ≤ᵐ[completionLaw n]
      (fun p => (1-lam)*vectorMeasurePotential μ β t p 0 + lam*vectorMeasurePotential ν β t p 0) := by
  apply ae_le_of_forall_setIntegral_le
    (integrable_vectorMeasurePotential _ β t ht 0)
    (((integrable_vectorMeasurePotential μ β t ht 0).const_mul (1-lam)).add
      ((integrable_vectorMeasurePotential ν β t ht 0).const_mul lam))
  intro S hS hSf
  let Z : VectorDisorderBrownianSample n → ℝ := fun sample => S.indicator (fun _ => (1 : ℝ)) sample.1
  have hZ : Measurable[vectorBrownianFiltration n 0] Z :=
    (measurable_const.indicator hS).comp (stronglyMeasurable_initialVectorDisorder n 0).measurable
  have hC : ∀sample,‖Z sample‖ ≤ (1 : ℝ≥0) := by
    intro sample; by_cases hp : sample.1 ∈ S <;> simp [Z,hp]
  have hZn : ∀sample,0 ≤ Z sample := by
    intro sample; by_cases hp : sample.1 ∈ S <;> simp [Z,hp]
  have hh := integral_vectorMeasurePotential_mix_le_weighted μ ν β t ht lam hlam Z hZ 1 hC hZn
  have he (ρ : Paper.ParisiMeasure) :
      (∫sample,Z sample*vectorMeasurePotential ρ β t sample.1 0 ∂vectorDisorderBrownianMeasure n) =
        ∫p in S,vectorMeasurePotential ρ β t p 0 ∂completionLaw n := by
    calc
      _ = ∫p,S.indicator (fun _ => (1 : ℝ)) p*vectorMeasurePotential ρ β t p 0 ∂completionLaw n :=
        integral_vectorInitialFunction _
      _ = _ := by
        rw [← integral_indicator hS]
        congr 1; funext p; by_cases hp : p ∈ S <;> simp [hp]
  rw [he,he,he] at hh
  simp only [Pi.add_apply]
  rw [integral_add ((integrable_vectorMeasurePotential μ β t ht 0).integrableOn.const_mul (1-lam))
    ((integrable_vectorMeasurePotential ν β t ht 0).integrableOn.const_mul lam),
    integral_const_mul,integral_const_mul]
  exact hh

theorem completionLaw_openPos (n : ℕ) : Measure.IsOpenPosMeasure (completionLaw n) := by
  letI : Measure.IsOpenPosMeasure (gaussianReal 0 1) :=
    (gaussianReal_absolutelyContinuous' 0 (by norm_num : (1 : ℝ≥0) ≠ 0)).isOpenPosMeasure
  letI : Measure.IsOpenPosMeasure (gaussianReal 0 (1/2)) :=
    (gaussianReal_absolutelyContinuous' 0 (by norm_num : (1/2 : ℝ≥0) ≠ 0)).isOpenPosMeasure
  unfold completionLaw couplingLaw Paper.skCouplingLaw
  infer_instance

theorem vectorMeasurePotential_mix_le (μ ν : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t ≤ 1) (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) 1)
    (p : Couplings n × ℝ) :
    vectorMeasurePotential (Paper.parisiMix μ ν lam) β t p 0 ≤
      (1-lam)*vectorMeasurePotential μ β t p 0 + lam*vectorMeasurePotential ν β t p 0 := by
  letI := completionLaw_openPos n
  let f : Couplings n × ℝ → ℝ := fun p => vectorMeasurePotential (Paper.parisiMix μ ν lam) β t p 0
  let g : Couplings n × ℝ → ℝ := fun p => (1-lam)*vectorMeasurePotential μ β t p 0 + lam*vectorMeasurePotential ν β t p 0
  have hc (ρ : Paper.ParisiMeasure) : Continuous (fun p : Couplings n × ℝ => vectorMeasurePotential ρ β t p 0) := by
    have hp : Continuous (fun p : Couplings n × ℝ => ((p,(0 : Field n)) : VectorParameter n)) :=
      continuous_id.prodMk continuous_const
    have hh := (continuous_vectorMeasurePotential_joint (n := n) ρ β t ht).comp hp
    simpa only [Function.comp_def] using hh
  have hclosed : IsClosed {p | f p ≤ g p} := isClosed_le (hc _) ((continuous_const.mul (hc μ)).add (continuous_const.mul (hc ν)))
  have hae : ∀ᵐp ∂completionLaw n,p ∈ {p | f p ≤ g p} :=
    vectorMeasurePotential_mix_ae_le μ ν β t ht lam hlam
  have he : {p | f p ≤ g p} = univ := hclosed.ae_eq_univ_iff_eq.mp (by
    filter_upwards [hae] with p hp
    exact propext (iff_true_intro hp))
  have hp : p ∈ {p | f p ≤ g p} := by rw [he]; exact mem_univ p
  exact hp

end QuantitativePaper
