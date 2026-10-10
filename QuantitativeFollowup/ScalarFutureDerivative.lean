module
public import QuantitativeFollowup.ScalarRestartJacobian
public import QuantitativeFollowup.ScalarFutureSquare
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

@[expose] public section

/-! The literal spatial derivative of the scalar conditional square
kernel is obtained by differentiating the actual restarted Picard flow. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper FourPapersCommon Filter
open scoped NNReal Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

def scalarFutureSquareDerivative (β : ℝ) (μ : Paper.ParisiMeasure)
    (r q : Paper.Overlap) (hrq : (r : ℝ) ≤ q) (x : ℝ) : ℝ :=
  ∫ W, 2*parisiGradient β μ (q,parisiPhysicalRestartEndpoint β μ r q hrq (x,W))*
    parisiHessian β μ (q,parisiPhysicalRestartEndpoint β μ r q hrq (x,W))*
    scalarRestartFlowJacobian β μ r r.property.1 x W ((q : ℝ)-r) ∂canonicalWienerMeasure

theorem measurable_scalarFutureSquareDerivative_integrand (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (r q : Paper.Overlap) (hrq : (r : ℝ) ≤ q) (x : ℝ) :
    Measurable (fun W => 2*parisiGradient β μ
      (q,parisiPhysicalRestartEndpoint β μ r q hrq (x,W))*parisiHessian β μ
      (q,parisiPhysicalRestartEndpoint β μ r q hrq (x,W))*
      scalarRestartFlowJacobian β μ r r.property.1 x W ((q : ℝ)-r)) := by
  have he : Measurable (fun W : C(Paper.Overlap,ℝ) =>
      parisiPhysicalRestartEndpoint β μ r q hrq (x,W)) :=
    (measurable_parisiPhysicalRestartEndpoint β hβ μ r q hrq).comp
      (measurable_const.prodMk measurable_id)
  exact ((measurable_const.mul ((continuous_parisiGradient β μ).measurable.comp
    (measurable_const.prodMk he))).mul ((continuous_parisiHessian_all β μ).measurable.comp
    (measurable_const.prodMk he))).mul
    (measurable_scalarRestartFlowJacobian β hβ μ r r.property.1 x _ (sub_nonneg.mpr hrq))

theorem scalarFutureSquareDerivative_integrand_bound (β : ℝ) (μ : Paper.ParisiMeasure)
    (r q : Paper.Overlap) (hrq : (r : ℝ) ≤ q) (x : ℝ) (W : C(Paper.Overlap,ℝ)) :
    ‖2*parisiGradient β μ (q,parisiPhysicalRestartEndpoint β μ r q hrq (x,W))*
      parisiHessian β μ (q,parisiPhysicalRestartEndpoint β μ r q hrq (x,W))*
      scalarRestartFlowJacobian β μ r r.property.1 x W ((q : ℝ)-r)‖ ≤ 2*Real.exp (β^2) := by
  have ht : (q : ℝ)-r∈Icc (0 : ℝ) 1 :=
    ⟨sub_nonneg.mpr hrq,by linarith [q.property.2,r.property.1]⟩
  have hj := scalarRestartFlowJacobian_pos_le β μ r r.property.1 x W _ ht
  rw [norm_mul,norm_mul,norm_mul,show ‖(2 : ℝ)‖=2 by norm_num,
    Real.norm_of_nonneg hj.1.le]
  have hg := norm_parisiGradient_le_one β μ (q,parisiPhysicalRestartEndpoint β μ r q hrq (x,W))
  have hh := norm_parisiHessian_le_one_all β μ (q,parisiPhysicalRestartEndpoint β μ r q hrq (x,W))
  exact (mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hg (by norm_num)) hh
    (norm_nonneg _) (by norm_num)) hj.2 hj.1.le (by norm_num)).trans_eq (by ring)

theorem hasDerivAt_scalarFutureSquare (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (r q : Paper.Overlap) (hrq : (r : ℝ) ≤ q) (x : ℝ) :
    HasDerivAt (scalarFutureSquare β μ r q hrq)
      (scalarFutureSquareDerivative β μ r q hrq x) x := by
  let F := fun y W => parisiGradient β μ (q,parisiPhysicalRestartEndpoint β μ r q hrq (y,W))^2
  let D := fun y W => 2*parisiGradient β μ (q,parisiPhysicalRestartEndpoint β μ r q hrq (y,W))*
    parisiHessian β μ (q,parisiPhysicalRestartEndpoint β μ r q hrq (y,W))*
    scalarRestartFlowJacobian β μ r r.property.1 y W ((q : ℝ)-r)
  have hFm (y : ℝ) : Measurable (F y) :=
    (((continuous_parisiGradient β μ).measurable.comp (measurable_const.prodMk
      ((measurable_parisiPhysicalRestartEndpoint β hβ μ r q hrq).comp
        (measurable_const.prodMk measurable_id)))).pow_const 2)
  have hi : Integrable (F x) canonicalWienerMeasure :=
    (integrable_const (1 : ℝ)).mono' (hFm x).aestronglyMeasurable (.of_forall fun W => by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) (norm_parisiGradient_le_one β μ _))
  have hdiff : ∀ᵐ W ∂canonicalWienerMeasure, ∀ y∈(univ : Set ℝ),
      HasDerivAt (fun z => F z W) (D y W) y := by
    apply Filter.Eventually.of_forall
    intro W y _
    have hd := ((hasDerivAt_parisiGradient_spatial_all β μ q
      (parisiPhysicalRestartEndpoint β μ r q hrq (y,W))).comp y
        (hasDerivAt_scalarPhysicalRestartEndpoint_initial β hβ μ r q hrq y W)).pow 2
    convert hd using 1 <;> dsimp only [F,D,Function.comp_def] <;>
      first | rfl | ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := D) (bound := fun _ => 2*Real.exp (β^2)) (s := univ) (by simp)
    (.of_forall fun y => (hFm y).aestronglyMeasurable) hi
    (measurable_scalarFutureSquareDerivative_integrand β hβ μ r q hrq x).aestronglyMeasurable
    (.of_forall fun W y _ => scalarFutureSquareDerivative_integrand_bound β μ r q hrq y W)
    (integrable_const _) hdiff).2

theorem norm_scalarFutureSquareDerivative_le (β : ℝ) (μ : Paper.ParisiMeasure)
    (r q : Paper.Overlap) (hrq : (r : ℝ) ≤ q) (x : ℝ) :
    ‖scalarFutureSquareDerivative β μ r q hrq x‖ ≤ 2*Real.exp (β^2) := by
  simpa only [scalarFutureSquareDerivative,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const (μ := canonicalWienerMeasure)
      (.of_forall fun W => scalarFutureSquareDerivative_integrand_bound β μ r q hrq x W)

theorem deriv_scalarFutureSquare (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (r q : Paper.Overlap) (hrq : (r : ℝ) ≤ q) :
    deriv (scalarFutureSquare β μ r q hrq) = scalarFutureSquareDerivative β μ r q hrq :=
  funext fun x => (hasDerivAt_scalarFutureSquare β hβ μ r q hrq x).deriv

theorem measurable_scalarFutureSquareDerivative (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (r q : Paper.Overlap) (hrq : (r : ℝ) ≤ q) :
    Measurable (scalarFutureSquareDerivative β μ r q hrq) := by
  rw [← deriv_scalarFutureSquare β hβ μ r q hrq]
  exact measurable_deriv _

end QuantitativeFollowup
