module
public import HexagonPaper.PathHeatSignedGeneratorLimits
public import HexagonPaper.PathHeatNormalizedLimit
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

/-! Jointly continuous source functionals and their signed derivatives.
This is a source-hypothesis record: its fields contain no Gaussian response,
integral differentiation, covariance identity or normalizer conclusion. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction NNReal
namespace HexagonPaper
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {X Θ : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [CompactSpace X] [SecondCountableTopology X]
  [TopologicalSpace Θ]

structure PathHeatContinuousSignedSource (Θ X : Type*) [TopologicalSpace Θ]
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [CompactSpace X] [SecondCountableTopology X] where
  ell : Θ→ℝ
  phi : Θ→ℝ
  dotell : Θ→ℝ
  dotphi : Θ→ℝ
  S : Θ→SignedMeasure X
  P : Θ→SignedMeasure X
  M : Θ→SignedMeasure (X×X)
  Q : Θ→SignedMeasure (X×X)
  B : ℝ≥0
  Ds : ℝ≥0
  Dm : ℝ≥0
  Dp : ℝ≥0
  Dq : ℝ≥0
  Dt : ℝ≥0
  Dphi : ℝ≥0
  continuous_ell : Continuous ell
  continuous_phi : Continuous phi
  continuous_dotell : Continuous dotell
  continuous_dotphi : Continuous dotphi
  continuous_S : ∀u,Tendsto (fun v=>signedTV (S v-S u)) (𝓝 u) (𝓝 0)
  continuous_P : ∀u,Tendsto (fun v=>signedTV (P v-P u)) (𝓝 u) (𝓝 0)
  continuous_M : ∀u,Tendsto (fun v=>signedTV (M v-M u)) (𝓝 u) (𝓝 0)
  continuous_Q : ∀u,Tendsto (fun v=>signedTV (Q v-Q u)) (𝓝 u) (𝓝 0)
  bound_phi : ∀u,|phi u|≤B
  bound_dotell : ∀u,|dotell u|≤Dt
  bound_dotphi : ∀u,|dotphi u|≤Dphi
  bound_S : ∀u,signedTV (S u)≤Ds
  bound_P : ∀u,signedTV (P u)≤Dp
  bound_M : ∀u,signedTV (M u)≤Dm
  bound_Q : ∀u,signedTV (Q u)≤Dq

namespace PathHeatContinuousSignedSource
variable (d : PathHeatContinuousSignedSource Θ X)

def weight (u : Θ) : ℝ := Real.exp (d.ell u)
def densityGenerator (K : X×X→ᵇℝ) (u : Θ) : ℝ :=
  pathHeatDensityGenerator K (d.S u) (d.M u) (d.dotell u)
def observableGenerator (K : X×X→ᵇℝ) (u : Θ) : ℝ :=
  pathHeatObservableGenerator K (d.S u) (d.P u) (d.Q u) (d.dotphi u)
def densityBound (κ : ℝ≥0) : ℝ := d.Dt+(1/2:ℝ)*κ*(d.Dm+d.Ds*d.Ds)
def observableBound (κ : ℝ≥0) : ℝ := d.Dphi+(1/2:ℝ)*κ*(d.Dq+2*d.Ds*d.Dp)

theorem continuous_weight : Continuous d.weight := Real.continuous_exp.comp d.continuous_ell

theorem densityBound_nonneg (κ : ℝ≥0) : 0≤d.densityBound κ := by
  unfold densityBound;positivity

theorem observableBound_nonneg (κ : ℝ≥0) : 0≤d.observableBound κ := by
  unfold observableBound;positivity

theorem densityGenerator_bound (K : X×X→ᵇℝ) (κ : ℝ≥0) (hK : ‖K‖≤κ) (u : Θ) :
    |d.densityGenerator K u|≤d.densityBound κ := by
  have hv := pathHeatDensityGenerator_bound K (d.S u) (d.M u) (d.dotell u)
  have hm := pathHeatDensityDerivativeMeasure_TV_bound (d.S u) (d.M u)
    d.Ds d.Dm d.Ds.coe_nonneg (d.bound_S u) (d.bound_M u)
  have hs2 : signedTV (d.S u)*signedTV (d.S u)≤(d.Ds:ℝ)*d.Ds :=
    mul_le_mul (d.bound_S u) (d.bound_S u) ENNReal.toReal_nonneg d.Ds.coe_nonneg
  have hsum : signedTV (d.M u)+signedTV (d.S u)*signedTV (d.S u)≤d.Dm+d.Ds*d.Ds :=
    add_le_add (d.bound_M u) hs2
  have hprod := mul_le_mul hK hsum
    (add_nonneg ENNReal.toReal_nonneg (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)) κ.coe_nonneg
  change _≤d.Dt+(1/2:ℝ)*κ*(d.Dm+d.Ds*d.Ds)
  rw [←Real.norm_eq_abs]
  exact hv.trans (by rw [Real.norm_eq_abs];nlinarith [d.bound_dotell u])

theorem observableGenerator_bound (K : X×X→ᵇℝ) (κ : ℝ≥0) (hK : ‖K‖≤κ) (u : Θ) :
    |d.observableGenerator K u|≤d.observableBound κ := by
  have hv := pathHeatObservableGenerator_bound K (d.S u) (d.P u) (d.Q u) (d.dotphi u)
  have hSP : signedTV (d.S u)*signedTV (d.P u)≤(d.Ds:ℝ)*d.Dp :=
    mul_le_mul (d.bound_S u) (d.bound_P u) ENNReal.toReal_nonneg d.Ds.coe_nonneg
  have hsum : signedTV (d.Q u)+2*signedTV (d.S u)*signedTV (d.P u)≤d.Dq+2*d.Ds*d.Dp := by
    nlinarith [d.bound_Q u]
  have hprod := mul_le_mul hK hsum
    (add_nonneg ENNReal.toReal_nonneg (mul_nonneg (mul_nonneg (by norm_num) ENNReal.toReal_nonneg)
      ENNReal.toReal_nonneg)) κ.coe_nonneg
  change _≤d.Dphi+(1/2:ℝ)*κ*(d.Dq+2*d.Ds*d.Dp)
  rw [←Real.norm_eq_abs]
  exact hv.trans (by rw [Real.norm_eq_abs];nlinarith [d.bound_dotphi u])

theorem tendsto_densityGenerator {A : Type*} {l : Filter A}
    (u : A→Θ) (u₀ : Θ) (K : A→X×X→ᵇℝ) (K₀ : X×X→ᵇℝ)
    (hu : Tendsto u l (𝓝 u₀)) (hK : Tendsto K l (𝓝 K₀)) :
    Tendsto (fun i=>d.densityGenerator (K i) (u i)) l (𝓝 (d.densityGenerator K₀ u₀)) :=
  tendsto_pathHeatDensityGenerator K K₀ (fun i=>d.S (u i)) (fun i=>d.M (u i))
    (d.S u₀) (d.M u₀) (fun i=>d.dotell (u i)) (d.dotell u₀) d.Ds d.Dm
    d.Ds.coe_nonneg d.Dm.coe_nonneg (fun i=>d.bound_S _) (fun i=>d.bound_M _) hK
    ((d.continuous_S u₀).comp hu) ((d.continuous_M u₀).comp hu)
    (d.continuous_dotell.continuousAt.tendsto.comp hu)

theorem tendsto_observableGenerator {A : Type*} {l : Filter A}
    (u : A→Θ) (u₀ : Θ) (K : A→X×X→ᵇℝ) (K₀ : X×X→ᵇℝ)
    (hu : Tendsto u l (𝓝 u₀)) (hK : Tendsto K l (𝓝 K₀)) :
    Tendsto (fun i=>d.observableGenerator (K i) (u i)) l (𝓝 (d.observableGenerator K₀ u₀)) :=
  tendsto_pathHeatObservableGenerator K K₀ (fun i=>d.S (u i)) (fun i=>d.P (u i))
    (fun i=>d.Q (u i)) (d.S u₀) (d.P u₀) (d.Q u₀) (fun i=>d.dotphi (u i))
    (d.dotphi u₀) d.Ds d.Dp d.Dq d.Ds.coe_nonneg d.Dp.coe_nonneg d.Dq.coe_nonneg
    (fun i=>d.bound_S _) (fun i=>d.bound_P _) (fun i=>d.bound_Q _) hK
    ((d.continuous_S u₀).comp hu) ((d.continuous_P u₀).comp hu) ((d.continuous_Q u₀).comp hu)
    (d.continuous_dotphi.continuousAt.tendsto.comp hu)

theorem continuous_densityGenerator (K : X×X→ᵇℝ) : Continuous (d.densityGenerator K) :=
  continuous_iff_continuousAt.mpr (fun u=>d.tendsto_densityGenerator id u (fun _=>K) K
    tendsto_id tendsto_const_nhds)

theorem continuous_observableGenerator (K : X×X→ᵇℝ) : Continuous (d.observableGenerator K) :=
  continuous_iff_continuousAt.mpr (fun u=>d.tendsto_observableGenerator id u (fun _=>K) K
    tendsto_id tendsto_const_nhds)

theorem moving_values {A : Type*} {l : Filter A}
    (u : A→Θ) (u₀ : Θ) (K : A→X×X→ᵇℝ) (K₀ : X×X→ᵇℝ)
    (hu : Tendsto u l (𝓝 u₀)) (hK : Tendsto K l (𝓝 K₀)) :
    Tendsto (fun i=>d.weight (u i)) l (𝓝 (d.weight u₀)) ∧
    Tendsto (fun i=>d.phi (u i)) l (𝓝 (d.phi u₀)) ∧
    Tendsto (fun i=>d.densityGenerator (K i) (u i)) l (𝓝 (d.densityGenerator K₀ u₀)) ∧
    Tendsto (fun i=>d.observableGenerator (K i) (u i)) l (𝓝 (d.observableGenerator K₀ u₀)) :=
  ⟨d.continuous_weight.continuousAt.tendsto.comp hu,
    d.continuous_phi.continuousAt.tendsto.comp hu,
    d.tendsto_densityGenerator u u₀ K K₀ hu hK,
    d.tendsto_observableGenerator u u₀ K K₀ hu hK⟩

theorem dominatedData [MeasurableSpace Θ] [BorelSpace Θ]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (u : Ω→Θ)
    (K : X×X→ᵇℝ) (κ : ℝ≥0) (hu : Measurable u) (hK : ‖K‖≤κ)
    (e : Ω→ℝ) (he : Integrable e μ) (hbound : ∀ω,d.weight (u ω)≤e ω) :
    PathHeatDominatedData μ (fun ω=>d.weight (u ω)) (fun ω=>d.phi (u ω))
      (fun ω=>d.densityGenerator K (u ω)) (fun ω=>d.observableGenerator K (u ω))
      e d.B (d.densityBound κ) (d.observableBound κ) where
  integrable_envelope := he
  nonneg_B := d.B.coe_nonneg
  nonneg_C := d.densityBound_nonneg κ
  nonneg_D := d.observableBound_nonneg κ
  weight_measurable := (d.continuous_weight.measurable.comp hu).aestronglyMeasurable
  observable_measurable := (d.continuous_phi.measurable.comp hu).aestronglyMeasurable
  density_generator_measurable := ((d.continuous_densityGenerator K).measurable.comp hu).aestronglyMeasurable
  observable_generator_measurable := ((d.continuous_observableGenerator K).measurable.comp hu).aestronglyMeasurable
  weight_positive := .of_forall (fun _=>Real.exp_pos _)
  weight_bound := .of_forall hbound
  observable_bound := .of_forall (fun _=>d.bound_phi _)
  density_generator_bound := .of_forall (fun _=>d.densityGenerator_bound K κ hK _)
  observable_generator_bound := .of_forall (fun _=>d.observableGenerator_bound K κ hK _)

end PathHeatContinuousSignedSource
end HexagonPaper
