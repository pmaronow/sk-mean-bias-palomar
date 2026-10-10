module
public import QuantitativeFollowup.ScalarRestartJacobianContinuity
public import QuantitativeFollowup.ScalarFutureDiagonal

@[expose] public section

/-! Actual future-square kernels and their spatial derivatives are jointly
continuous in the weak profile, both levels, and the initial field.  An
irrelevant extension to reversed levels avoids introducing discontinuous
proof-dependent domains.  It agrees with the actual kernel for r ≤ q. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper FourPapersCommon
open scoped NNReal Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false

abbrev ScalarFutureParameters := Paper.ParisiMeasure×(Paper.Overlap×(Paper.Overlap×ℝ))

def scalarFutureEndpointExtended (β : ℝ) (μ : Paper.ParisiMeasure)
    (r q : Paper.Overlap) (x : ℝ) (W : C(Paper.Overlap,ℝ)) : ℝ :=
  parisiRestartNoiseStatePath β x μ r r.property.1 W (projIcc 0 1 zero_le_one ((q : ℝ)-r))

def scalarFutureJacobianExtended (β : ℝ) (μ : Paper.ParisiMeasure)
    (r q : Paper.Overlap) (x : ℝ) (W : C(Paper.Overlap,ℝ)) : ℝ :=
  scalarRestartFlowJacobian β μ r r.property.1 x W
    (projIcc 0 1 zero_le_one ((q : ℝ)-r))

def scalarFutureSquareExtended (β : ℝ) (μ : Paper.ParisiMeasure)
    (r q : Paper.Overlap) (x : ℝ) : ℝ :=
  ∫ W,parisiGradient β μ (q,scalarFutureEndpointExtended β μ r q x W)^2 ∂canonicalWienerMeasure

def scalarFutureSquareDerivativeExtended (β : ℝ) (μ : Paper.ParisiMeasure)
    (r q : Paper.Overlap) (x : ℝ) : ℝ :=
  ∫ W,2*parisiGradient β μ (q,scalarFutureEndpointExtended β μ r q x W)*
    parisiHessian β μ (q,scalarFutureEndpointExtended β μ r q x W)*
      scalarFutureJacobianExtended β μ r q x W ∂canonicalWienerMeasure

theorem continuous_scalarFutureEndpointExtended (β : ℝ) :
    Continuous (fun z : ScalarFutureParameters×C(Paper.Overlap,ℝ) =>
      scalarFutureEndpointExtended β z.1.1 z.1.2.1 z.1.2.2.1 z.1.2.2.2 z.2) := by
  have harg : Continuous (fun z : ScalarFutureParameters×C(Paper.Overlap,ℝ) =>
      (z.1.1,(z.1.2.1,(z.1.2.2.2,z.2)))) := by fun_prop
  have hp := (continuous_scalarRestartNoiseStatePath β).comp harg
  have ht : Continuous (fun z : ScalarFutureParameters×C(Paper.Overlap,ℝ) =>
      projIcc 0 1 zero_le_one ((z.1.2.2.1 : ℝ)-z.1.2.1)) :=
    (continuous_projIcc (a := (0 : ℝ)) (b := 1) (h := zero_le_one)).comp (by fun_prop)
  convert! continuous_eval.comp (hp.prodMk ht) using 1

theorem continuous_scalarFutureJacobianExtended (β : ℝ) (hβ : β ≠ 0) :
    Continuous (fun z : ScalarFutureParameters×C(Paper.Overlap,ℝ) =>
      scalarFutureJacobianExtended β z.1.1 z.1.2.1 z.1.2.2.1 z.1.2.2.2 z.2) := by
  have harg : Continuous (fun z : ScalarFutureParameters×C(Paper.Overlap,ℝ) =>
      (z.1.1,(z.1.2.1,(z.1.2.2.2,(z.2,projIcc 0 1 zero_le_one ((z.1.2.2.1 : ℝ)-z.1.2.1)))))) := by fun_prop
  convert! (continuous_scalarRestartFlowJacobian β hβ).comp harg using 1

theorem continuous_scalarFutureSquare_integrand (β : ℝ) :
    Continuous (fun z : ScalarFutureParameters×C(Paper.Overlap,ℝ) =>
      parisiGradient β z.1.1 (z.1.2.2.1,
        scalarFutureEndpointExtended β z.1.1 z.1.2.1 z.1.2.2.1 z.1.2.2.2 z.2)^2) := by
  have harg : Continuous (fun z : ScalarFutureParameters×C(Paper.Overlap,ℝ) =>
      (z.1.1,((z.1.2.2.1 : ℝ),scalarFutureEndpointExtended β z.1.1 z.1.2.1 z.1.2.2.1 z.1.2.2.2 z.2))) :=
    (continuous_fst.comp continuous_fst).prodMk
      ((continuous_subtype_val.comp (continuous_fst.comp (continuous_snd.comp (continuous_snd.comp continuous_fst)))).prodMk
        (continuous_scalarFutureEndpointExtended β))
  convert! ((continuous_parisiGradient_measure_joint β).comp harg).pow 2 using 1

theorem continuous_scalarFutureSquareDerivative_integrand (β : ℝ) (hβ : β ≠ 0) :
    Continuous (fun z : ScalarFutureParameters×C(Paper.Overlap,ℝ) =>
      2*parisiGradient β z.1.1 (z.1.2.2.1,
        scalarFutureEndpointExtended β z.1.1 z.1.2.1 z.1.2.2.1 z.1.2.2.2 z.2)*
      parisiHessian β z.1.1 (z.1.2.2.1,
        scalarFutureEndpointExtended β z.1.1 z.1.2.1 z.1.2.2.1 z.1.2.2.2 z.2)*
      scalarFutureJacobianExtended β z.1.1 z.1.2.1 z.1.2.2.1 z.1.2.2.2 z.2) := by
  have hp : Continuous (fun z : ScalarFutureParameters×C(Paper.Overlap,ℝ) =>
      (z.1.1,((z.1.2.2.1 : ℝ),scalarFutureEndpointExtended β z.1.1 z.1.2.1 z.1.2.2.1 z.1.2.2.2 z.2))) :=
    (continuous_fst.comp continuous_fst).prodMk
      ((continuous_subtype_val.comp (continuous_fst.comp (continuous_snd.comp (continuous_snd.comp continuous_fst)))).prodMk
        (continuous_scalarFutureEndpointExtended β))
  convert! ((continuous_const.mul ((continuous_parisiGradient_measure_joint β).comp hp)).mul
    ((continuous_parisiHessian_measure_joint β hβ).comp hp)).mul
      (continuous_scalarFutureJacobianExtended β hβ) using 1

theorem scalarFutureSquareDerivativeExtended_integrand_bound (β : ℝ)
    (μ : Paper.ParisiMeasure) (r q : Paper.Overlap) (x : ℝ) (W : C(Paper.Overlap,ℝ)) :
    ‖2*parisiGradient β μ (q,scalarFutureEndpointExtended β μ r q x W)*
      parisiHessian β μ (q,scalarFutureEndpointExtended β μ r q x W)*
      scalarFutureJacobianExtended β μ r q x W‖ ≤ 2*Real.exp (β^2) := by
  have hj := scalarRestartFlowJacobian_pos_le β μ r r.property.1 x W
    (projIcc 0 1 zero_le_one ((q : ℝ)-r)) (projIcc 0 1 zero_le_one ((q : ℝ)-r)).property
  change 0 < scalarFutureJacobianExtended β μ r q x W ∧
    scalarFutureJacobianExtended β μ r q x W ≤ Real.exp (β^2) at hj
  rw [norm_mul,norm_mul,norm_mul,show ‖(2 : ℝ)‖=2 by norm_num,Real.norm_of_nonneg hj.1.le]
  have hg := norm_parisiGradient_le_one β μ (q,scalarFutureEndpointExtended β μ r q x W)
  have hh := norm_parisiHessian_le_one_all β μ (q,scalarFutureEndpointExtended β μ r q x W)
  exact (mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hg (by norm_num)) hh
    (norm_nonneg _) (by norm_num)) hj.2 hj.1.le (by norm_num)).trans_eq (by ring)

theorem continuous_scalarFutureSquareExtended (β : ℝ) :
    Continuous (fun p : ScalarFutureParameters => scalarFutureSquareExtended β p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  apply continuous_of_dominated (μ := canonicalWienerMeasure) (bound := fun _ => (1 : ℝ))
  · intro p
    have harg : Continuous (fun W : C(Paper.Overlap,ℝ) => (p,W)) := continuous_const.prodMk continuous_id
    convert! ((continuous_scalarFutureSquare_integrand β).comp harg).measurable.aestronglyMeasurable using 1
  · intro p
    exact .of_forall fun W => by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) (norm_parisiGradient_le_one β p.1 _)
  · exact integrable_const _
  · apply Filter.Eventually.of_forall
    intro W
    have harg : Continuous (fun p : ScalarFutureParameters => (p,W)) := continuous_id.prodMk continuous_const
    convert! (continuous_scalarFutureSquare_integrand β).comp harg using 1

theorem continuous_scalarFutureSquareDerivativeExtended (β : ℝ) (hβ : β ≠ 0) :
    Continuous (fun p : ScalarFutureParameters => scalarFutureSquareDerivativeExtended β p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  apply continuous_of_dominated (μ := canonicalWienerMeasure) (bound := fun _ => 2*Real.exp (β^2))
  · intro p
    have harg : Continuous (fun W : C(Paper.Overlap,ℝ) => (p,W)) := continuous_const.prodMk continuous_id
    convert! ((continuous_scalarFutureSquareDerivative_integrand β hβ).comp harg).measurable.aestronglyMeasurable using 1
  · intro p
    exact .of_forall fun W => scalarFutureSquareDerivativeExtended_integrand_bound β p.1 p.2.1 p.2.2.1 p.2.2.2 W
  · exact integrable_const _
  · apply Filter.Eventually.of_forall
    intro W
    have harg : Continuous (fun p : ScalarFutureParameters => (p,W)) := continuous_id.prodMk continuous_const
    convert! (continuous_scalarFutureSquareDerivative_integrand β hβ).comp harg using 1

theorem scalarFutureEndpointExtended_eq (β : ℝ) (μ : Paper.ParisiMeasure)
    (r q : Paper.Overlap) (hrq : (r : ℝ) ≤ q) (x : ℝ) (W : C(Paper.Overlap,ℝ)) :
    scalarFutureEndpointExtended β μ r q x W=parisiPhysicalRestartEndpoint β μ r q hrq (x,W) := by
  simp only [scalarFutureEndpointExtended,parisiPhysicalRestartEndpoint,
    parisiElapsedOverlap,projIcc_of_mem zero_le_one
      (show (q : ℝ)-r∈Icc (0 : ℝ) 1 from ⟨sub_nonneg.mpr hrq,by linarith [q.property.2,r.property.1]⟩)]

theorem scalarFutureSquareExtended_eq (β : ℝ) (μ : Paper.ParisiMeasure)
    (r q : Paper.Overlap) (hrq : (r : ℝ) ≤ q) (x : ℝ) :
    scalarFutureSquareExtended β μ r q x=scalarFutureSquare β μ r q hrq x := by
  simp only [scalarFutureSquareExtended,scalarFutureSquare,scalarTransitionExpectation,
    scalarFutureEndpointExtended_eq β μ r q hrq]

theorem scalarFutureSquareDerivativeExtended_eq (β : ℝ) (μ : Paper.ParisiMeasure)
    (r q : Paper.Overlap) (hrq : (r : ℝ) ≤ q) (x : ℝ) :
    scalarFutureSquareDerivativeExtended β μ r q x=scalarFutureSquareDerivative β μ r q hrq x := by
  simp only [scalarFutureSquareDerivativeExtended,scalarFutureSquareDerivative,
    scalarFutureEndpointExtended_eq β μ r q hrq,scalarFutureJacobianExtended,
    projIcc_of_mem zero_le_one
      (show (q : ℝ)-r∈Icc (0 : ℝ) 1 from ⟨sub_nonneg.mpr hrq,by linarith [q.property.2,r.property.1]⟩)]

end QuantitativeFollowup
