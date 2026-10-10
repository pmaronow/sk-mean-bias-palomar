module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseLastVarianceFeatures
public import QuantitativeFollowup.FollowupCavityCppZeroResponseScalar
public import QuantitativeFollowup.FollowupCavityFixedRowObservableBounds

@[expose] public section

/-! Literal retained-node scalar/rest observables separate under the
actual finite recursion for every independently varied last variance. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {k : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

open OverlapPaper

theorem cavityLastVariance_depthExpectation_product (s : RSBScheme k) (n : ℕ) (β ρ : ℝ)
    (hβ : 0 < β) (hρ : ρ ∈ Ioc (0 : ℝ) 1) (v : ℝ) (hv : 0 < v) (p j : ℕ)
    (f : AnisotropicParameter n → ℝ) (b : ℝ → ℝ)
    (hf : Measurable f) (hb : Measurable b) (P : AnisotropicParameter (n+1)) :
    sourceKernelExpectation
      (fun r => anisotropicDepthKernel (cavityLastVarianceModel n β ρ hβ hρ v hv) s (p+r)) j
      (fun Q => f (cavityRestParameterProjection n Q)*b (Q (Sum.inr (Fin.last n)))) P =
    sourceKernelExpectation
      (fun r => anisotropicDepthKernel (followupCavityRestSpinModel n β ρ hβ hρ) s (p+r)) j f
      (cavityRestParameterProjection n P) *
    sourceKernelExpectation (fun r => cavityScalarDepthKernel s (Real.sqrt v) (p+r)) j b
      (P (Sum.inr (Fin.last n))) := by
  let D := cavityLastVarianceModel n β ρ hβ hρ v hv
  let R := followupCavityRestSpinModel n β ρ hβ hρ
  let β0 := Real.sqrt v
  induction j generalizing P with
  | zero => rfl
  | succ j ih =>
      simp only [sourceKernelExpectation]
      simp_rw [ih]
      let g : AnisotropicDisorder (n+1) := WithLp.toLp 2 (fun e => P (Sum.inl e))
      let x : QuantitativePaper.Field (n+1) := WithLp.toLp 2 (fun i => P (Sum.inr i))
      have hid : anisotropicParameterPoint g x = P := by ext i; cases i <;> rfl
      have hm : Measurable (fun z : AnisotropicParameter n × ℝ =>
          sourceKernelExpectation (fun r => anisotropicDepthKernel R s (p+r)) j f z.1 *
          sourceKernelExpectation (fun r => cavityScalarDepthKernel s β0 (p+r)) j b z.2) :=
        ((sourceKernelExpectation_measurable _ f hf j).comp measurable_fst).mul
          ((sourceKernelExpectation_measurable _ b hb j).comp measurable_snd)
      change (∫ Q, (fun z : AnisotropicParameter n × ℝ =>
          sourceKernelExpectation (fun r => anisotropicDepthKernel R s (p+r)) j f z.1 *
          sourceKernelExpectation (fun r => cavityScalarDepthKernel s β0 (p+r)) j b z.2)
        (cavityIndependentParameterSplit n Q) ∂anisotropicDepthKernel D s (p+j) P) = _
      rw [←integral_map (measurable_cavityIndependentParameterSplit n).aemeasurable hm.aestronglyMeasurable,
        ←hid,cavityLastVariance_depthKernel_product,integral_prod_mul,cavityRestParameterProjection_point]
      rfl


end QuantitativeFollowup
