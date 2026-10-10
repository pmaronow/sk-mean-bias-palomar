module
public import QuantitativePaper.VectorDyadicGradient
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv

@[expose] public section

/-! Actual spatial differentiation of the constructed arbitrary-profile
vector potential, and its bounded measurable Lipschitz gradient. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 400000

theorem hasFDerivAt_vectorMeasureTailPotential {n : ℕ} (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n) :
    HasFDerivAt (vectorMeasureTailPotential μ β t q p)
      ((InnerProductSpace.toDual ℝ (Field n)) (vectorMeasureGradient μ β t q p x)) x := by
  have hG := (tendstoUniformly_vectorDyadicTailGradient μ β t ht).comp
    (fun y : Field n => (q,(p,y)))
  have hD := (InnerProductSpace.toDual ℝ (Field n)).isometry.uniformContinuous.comp_tendstoUniformly hG
  apply hasFDerivAt_of_tendstoUniformly hD
  · intro j y
    have hh := (differentiable_vectorDyadicTailPotential μ β t q j p y).hasFDerivAt
    simpa only [Function.comp_def,vectorDyadicTailGradient_eq_gradient,toDual_gradient] using hh
  · intro y
    exact tendsto_vectorDyadicTailPotential μ β t q ht q.property p y

theorem vectorMeasureGradient_eq_gradient {n : ℕ} (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n) :
    vectorMeasureGradient μ β t q p x=gradient (vectorMeasureTailPotential μ β t q p) x := by
  simpa only [LinearIsometryEquiv.symm_apply_apply] using
    (hasFDerivAt_vectorMeasureTailPotential μ β t ht q p x).hasGradientAt.gradient.symm

theorem norm_vectorMeasureGradient_le {n : ℕ} (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n) :
    ‖vectorMeasureGradient μ β t q p x‖≤Real.sqrt (n : ℝ) := by
  apply le_of_tendsto (tendsto_vectorDyadicTailGradient μ β t ht q p x).norm
  exact Eventually.of_forall (fun j => norm_vectorFiniteTailGradient_le _ β t q p x)

theorem vectorMeasureGradient_lipschitz {n : ℕ} (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (q : Paper.Overlap) (p : Couplings n×ℝ) :
    LipschitzWith (n : ℝ≥0) (vectorMeasureGradient μ β t q p) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply le_of_tendsto
    ((tendsto_vectorDyadicTailGradient μ β t ht q p x).dist
      (tendsto_vectorDyadicTailGradient μ β t ht q p y))
  exact Eventually.of_forall (fun j =>
    (vectorFiniteTailGradient_lipschitz _ β t q p).dist_le_mul x y)

theorem measurable_vectorMeasureGradient {n : ℕ} (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) :
    Measurable (fun z : Paper.Overlap×VectorParameter n =>
      vectorMeasureGradient μ β t z.1 z.2.1 z.2.2) := by
  apply measurable_of_tendsto_metrizable
    (fun j => measurable_vectorFiniteTailGradient _ β t)
  apply tendsto_pi_nhds.mpr
  intro z
  exact tendsto_vectorDyadicTailGradient μ β t ht z.1 z.2.1 z.2.2

theorem vectorMeasureGradient_uniform_comparison {n : ℕ} (μ ν : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (q : Paper.Overlap) (p : Couplings n×ℝ)
    (δ : ℝ) (hδ : 0<δ) (x : Field n) :
    ‖vectorMeasureGradient μ β t q p x-vectorMeasureGradient ν β t q p x‖≤
      2*((n : ℝ)*((1-t)*β^2)*Paper.parisiCDFDistance μ ν)/δ+2*n*δ := by
  have hμ : vectorMeasureGradient μ β t q p=gradient (vectorMeasureTailPotential μ β t q p) :=
    funext (vectorMeasureGradient_eq_gradient μ β t ht q p)
  have hν : vectorMeasureGradient ν β t q p=gradient (vectorMeasureTailPotential ν β t q p) :=
    funext (vectorMeasureGradient_eq_gradient ν β t ht q p)
  have hD := Paper.parisiCDFDistance_nonneg μ ν
  have hh := norm_gradient_sub_le_of_uniform_sub
    (vectorMeasureTailPotential μ β t q p) (vectorMeasureTailPotential ν β t q p)
    (fun y => (hasFDerivAt_vectorMeasureTailPotential μ β t ht q p y).differentiableAt)
    (fun y => (hasFDerivAt_vectorMeasureTailPotential ν β t ht q p y).differentiableAt)
    (n : ℝ≥0)
    (by simpa only [←hμ] using
      vectorMeasureGradient_lipschitz μ β t ht q p)
    (by simpa only [←hν] using
      vectorMeasureGradient_lipschitz ν β t ht q p)
    ((n : ℝ)*((1-t)*β^2)*Paper.parisiCDFDistance μ ν)
    (by positivity)
    (fun y => vectorMeasureTailPotential_CDFDistance_abs_sub_le μ ν β t q ht q.property p y)
    δ hδ x
  simpa only [←hμ,←hν,NNReal.coe_natCast] using hh

end QuantitativePaper
