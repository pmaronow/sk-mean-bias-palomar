module
public import HexagonPaper.CavityFixedRowRelativeRoot
public import FourPapersCommon.KernelSamplingMap
public import Mathlib.Probability.Kernel.Composition.WithDensity

@[expose] public section

/-! Genuine fulljoint lifting of the Gaussian root relative density and
the actual child likelihood ratio. This lemma performs only kernel and
measure composition; physical child ratios are instantiated separately. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon
open scoped ENNReal
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency true
variable {S I : Type} [Fintype S] [Fintype I] {Y : Type} [MeasurableSpace Y]

theorem cavityGaussianRootJoint_relative_from_child (U : FiniteStateField S → ℝ)
    {C : NNReal} (hU : LipschitzWith C U) (a : ℝ)
    (R : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) (H : FiniteStateField S)
    (K : Kernel (FiniteStateField S) Y) [IsMarkovKernel K]
    (tr : Y → Y) (htr : Measurable tr) (g : FiniteStateField S → Y → ℝ≥0∞)
    (hg : Measurable (Function.uncurry g)) (hgf : ∀ Q y, g Q y ≠ ∞)
    (hchild : ∀ Q, ((K Q).withDensity (g Q)).map tr = K (Q + H)) :
    cavityGaussianRootJoint U a R H K =
      ((cavityGaussianRootJoint U a R 0 K).withDensity
        (fun z => ENNReal.ofReal (Real.exp (a * (U (z.1 + H) - U z.1)) *
          cavityGaussianRootNormalizer U a R 0 / cavityGaussianRootNormalizer U a R H) *
          g z.1 z.2)).map (Prod.map (fun Q => Q + H) tr) := by
  haveI := isProbabilityMeasure_finiteStateGaussianStepLaw a R U hU.continuous.measurable 0
    (integrable_exp_finiteStateGaussian_lipschitz U hU R 0 a)
  haveI : IsSFiniteKernel (K.withDensity g) := Kernel.IsSFiniteKernel.withDensity K hgf
  let w := fun Q => ENNReal.ofReal (Real.exp (a * (U (Q + H) - U Q)) *
    cavityGaussianRootNormalizer U a R 0 / cavityGaussianRootNormalizer U a R H)
  have hw : Measurable w :=
    (((((hU.continuous.measurable.comp (measurable_id.add_const H)).sub
      hU.continuous.measurable).const_mul a).exp.mul_const _).div_const _).ennreal_ofReal
  have he := map_compProd_map_pair ((finiteStateGaussianStepLaw a R U 0).withDensity w)
    (K.withDensity g) K (fun Q => Q + H) tr (measurable_id.add_const H) htr
    (fun Q => by rw [Kernel.withDensity_apply _ hg]; exact hchild Q)
  rw [Measure.withDensity_compProd_withDensity hw hg] at he
  unfold cavityGaussianRootJoint
  rw [cavityGaussianRoot_relative_density U hU a R H]
  exact he.symm

end HexagonPaper
