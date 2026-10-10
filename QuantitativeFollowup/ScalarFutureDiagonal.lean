module
public import QuantitativeFollowup.ScalarFutureDerivative

@[expose] public section

/-! Exact diagonal values of the scalar response kernels.  The fresh
Wiener path starts at zero under its constructed law, so the restart
kernel at equal levels is the identity kernel. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper FourPapersCommon
open scoped NNReal Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

theorem scalarPhysicalRestartEndpoint_self (β : ℝ) (μ : Paper.ParisiMeasure)
    (r : Paper.Overlap) (x : ℝ) (W : C(Paper.Overlap,ℝ)) :
    parisiPhysicalRestartEndpoint β μ r r le_rfl (x,W)=x+β*W ⟨0,by norm_num⟩ := by
  rw [scalarPhysicalRestartEndpoint_eq_flow,sub_self]
  have he := scalarRestartFlow_equation β μ r r.property.1 x W 0 (by norm_num)
  simpa only [intervalIntegral.integral_same,add_zero,parisiNoiseExtension,
    projIcc_of_mem zero_le_one (show (0 : ℝ)∈Icc 0 1 by norm_num)] using he

theorem scalarTransitionExpectation_self (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (r : Paper.Overlap) (F : ℝ → ℝ)
    (hF : Measurable F) (x : ℝ) :
    scalarTransitionExpectation β μ r r le_rfl F x=F x := by
  have hm : Measurable (fun W : C(Paper.Overlap,ℝ) =>
      F (parisiPhysicalRestartEndpoint β μ r r le_rfl (x,W))) :=
    hF.comp ((measurable_parisiPhysicalRestartEndpoint β hβ μ r r le_rfl).comp
      (measurable_const.prodMk measurable_id))
  unfold scalarTransitionExpectation canonicalWienerMeasure
  rw [integral_map measurable_canonicalBrownianPath.aemeasurable hm.aestronglyMeasurable]
  simp only [scalarPhysicalRestartEndpoint_self,canonicalBrownianPath_zero,mul_zero,add_zero,
    integral_const,probReal_univ,smul_eq_mul,one_mul]

theorem scalarFutureSquare_self (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (r : Paper.Overlap) (x : ℝ) :
    scalarFutureSquare β μ r r le_rfl x=parisiGradient β μ (r,x)^2 :=
  scalarTransitionExpectation_self β hβ μ r _
    (((continuous_parisiGradient β μ).measurable.comp
      (measurable_const.prodMk measurable_id)).pow_const 2) x

theorem scalarFutureSquareDerivative_self (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (r : Paper.Overlap) (x : ℝ) :
    scalarFutureSquareDerivative β μ r r le_rfl x=
      2*parisiGradient β μ (r,x)*parisiHessian β μ (r,x) := by
  have he : scalarFutureSquare β μ r r le_rfl=(fun y => parisiGradient β μ (r,y)^2) :=
    funext (scalarFutureSquare_self β hβ μ r)
  have hd := hasDerivAt_scalarFutureSquare β hβ μ r r le_rfl x
  rw [he] at hd
  have hg := (hasDerivAt_parisiGradient_spatial_all β μ r x).pow 2
  have hd' : HasDerivAt (fun y => parisiGradient β μ (r,y)^2)
      (2*parisiGradient β μ (r,x)*parisiHessian β μ (r,x)) x := by
    convert hg using 1 <;> first | rfl | norm_num
  exact hd.unique hd'

end QuantitativeFollowup
