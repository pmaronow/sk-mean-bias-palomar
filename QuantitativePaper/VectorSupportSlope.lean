module
public import QuantitativePaper.VectorMeanOverlapDifferentiation
public import QuantitativePaper.VectorMeanOverlapNorm
public import QuantitativePaper.VectorMeasureCovarianceTrace
public import FRSB.Optimality

@[expose] public section

/-! Actual free-support slope and squared-Hessian contact bounds, including
overlap zero. The global differentiable primitive is used only for interval
calculus and is identified with the physical moment on the closed strip. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal Topology
namespace QuantitativePaper
open QuantitativeFollowup
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem vector_free_support_slope_le_one (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s : ℝ) (hs : s∈Ico (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (ha : 0≤a)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t a≤vectorMeasureFunctional n ν β t a)
    (q : Paper.Overlap) (hq : q∈(parisiFreeMeasure μ s).support) :
    vectorMeanOverlapDerivative (n:=n) μ β t a ht.le q≤1 := by
  have hcontact:=vector_free_support_contact hn μ s hs hμ β t a hβ ht ha hmin q hq
  have harg:=(vector_minimum_iff_free_support_argmin hn μ s ⟨hs.1,hs.2.le⟩ hs.2
    hμ β t a hβ ht ha).mp hmin hq
  have hfixed:vectorMeanOverlapPrimitive (n:=n) μ β t a ht.le q=(q : ℝ):=by
    rw [vectorMeanOverlapPrimitive_eq μ β t a hβ ht q.property]
    unfold vectorMeanOverlapReal
    rw [projIcc_of_mem zero_le_one q.property]
    exact hcontact.2
  have he:=FRSB.curvature_le_one_at_stationary_min
    (vectorMeanOverlapPrimitive (n:=n) μ β t a ht.le)
    (fun x=>vectorMeanOverlapDerivative (n:=n) μ β t a ht.le (projIcc (0 : ℝ) 1 zero_le_one x))
    (vectorOverlapPotentialPrimitive (n:=n) μ β t a ht.le)
    (continuous_vectorMeanOverlapDerivativeReal μ β t a ht.le)
    (hasDerivAt_vectorMeanOverlapPrimitive μ β t a ht.le) 1 (by norm_num)
    (fun x=>by simpa only [one_mul] using hasDerivAt_vectorOverlapPotentialPrimitive (n:=n) μ β t a ht.le x)
    hcontact.1 hfixed (by
      intro r hr
      have hr01:r∈Icc (0 : ℝ) 1:=⟨q.property.1.trans hr.1,hr.2⟩
      rw [vectorOverlapPotentialPrimitive_eq_deficit μ β t a hβ ht q.property,
        vectorOverlapPotentialPrimitive_eq_deficit μ β t a hβ ht hr01]
      exact harg ⟨r,hr01⟩)
  simpa only [projIcc_of_mem zero_le_one q.property] using he

theorem vector_free_support_hessian_energy_bound (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s : ℝ) (hs : s∈Ico (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (ha : 0≤a)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t a≤vectorMeasureFunctional n ν β t a)
    (q : Paper.Overlap) (hq : q∈(parisiFreeMeasure μ s).support) :
    (∫sample : VectorDisorderBrownianSample n,vectorMeasureHessianEnergy μ β t ht.le q sample
      ∂vectorMeasureDisorderTilt μ β t a)≤(n : ℝ)/((1-t)*β^2) := by
  have he:=vector_free_support_slope_le_one hn μ s hs hμ β t a hβ ht ha hmin q hq
  have hc:0<(1-t)*β^2:=mul_pos (sub_pos.mpr ht) (sq_pos_of_ne_zero hβ)
  have hn':0<(n : ℝ):=by positivity
  unfold vectorMeanOverlapDerivative at he
  have hh:((1-t)*β^2*(∫sample : VectorDisorderBrownianSample n,vectorMeasureHessianEnergy μ β t ht.le q sample
      ∂vectorMeasureDisorderTilt μ β t a))/(n : ℝ)≤1:=by
    simpa only [div_mul_eq_mul_div] using he
  have hb:((1-t)*β^2)*(∫sample : VectorDisorderBrownianSample n,vectorMeasureHessianEnergy μ β t ht.le q sample
      ∂vectorMeasureDisorderTilt μ β t a)≤(n : ℝ):=by
    simpa only [one_mul] using (div_le_iff₀ hn').mp hh
  exact (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hb)

theorem vector_free_support_trace_hessian_square_bound (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s : ℝ) (hs : s∈Ico (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (ha : 0≤a)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t a≤vectorMeasureFunctional n ν β t a)
    (q : Paper.Overlap) (hq : q∈(parisiFreeMeasure μ s).support) :
    (∫sample : VectorDisorderBrownianSample n,
      Matrix.trace (vectorMeasureHessianMatrix μ β t ht.le q sample*vectorMeasureHessianMatrix μ β t ht.le q sample)
      ∂vectorMeasureDisorderTilt μ β t a)≤(n : ℝ)/((1-t)*β^2) := by
  simp_rw [vectorMeasureHessianMatrix_trace_square]
  exact vector_free_support_hessian_energy_bound hn μ s hs hμ β t a hβ ht ha hmin q hq

end QuantitativePaper
