module
public import QuantitativePaper.VectorSupportSlope
public import QuantitativePaper.VectorMeasurePhysicalConditionalVariance

@[expose] public section

/-! Proposition 2.1 on the actual normalized disorder/field/spin law.
The spin mean and covariance are the genuine conditional moments in the
retained Wiener past, not auxiliary matrices supplied as assumptions. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Matrix
open scoped NNReal MatrixOrder
namespace QuantitativePaper
open QuantitativeFollowup
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem vectorMeasure_physical_matrix_order (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (hβ : β≠0) (ht : t<1) (q : Paper.Overlap) :
    ∀ᵐp ∂vectorMeasureSpinPathLaw (n:=n) μ β t a ht.le,
      (vectorMeasureSpinCovariance μ β t a ht.le q p.1).PosSemidef ∧
      (vectorMeasureHessianMatrix μ β t ht.le q p.1-
        Paper.parisiCDF μ q • vectorMeasureSpinCovariance μ β t a ht.le q p.1).PosSemidef ∧
      (vectorMeasureSpinCovariance μ β t a ht.le q p.1-
        vectorMeasureHessianMatrix μ β t ht.le q p.1).PosSemidef :=
  (measurePreserving_vectorMeasureSpinPathLaw_fst μ β t a ht.le).quasiMeasurePreserving.ae
    (vectorMeasure_matrix_order μ β t a hβ ht q)

theorem vector_free_support_physical_contact (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s : ℝ) (hs : s∈Ico (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (ha : 0≤a)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t a≤vectorMeasureFunctional n ν β t a)
    (q : Paper.Overlap) (hq : q∈(parisiFreeMeasure μ s).support) :
    (q:ℝ)<1 ∧
    (∫p : VectorDisorderBrownianSample n×Configuration n,‖vectorMeasureSpinMean (n:=n) μ β t ht.le q p.1‖^2
      ∂vectorMeasureSpinPathLaw μ β t a ht.le)=(n:ℝ)*(q:ℝ) ∧
    (∫p : VectorDisorderBrownianSample n×Configuration n,Matrix.trace (vectorMeasureHessianMatrix μ β t ht.le q p.1*
      vectorMeasureHessianMatrix μ β t ht.le q p.1)
      ∂vectorMeasureSpinPathLaw μ β t a ht.le)≤(n:ℝ)/((1-t)*β^2) := by
  refine ⟨(vector_free_support_contact hn μ s hs hμ β t a hβ ht ha hmin q hq).1,?_,?_⟩
  · have hm : Measurable (fun sample : VectorDisorderBrownianSample n=>
        ‖vectorMeasureSpinMean μ β t ht.le q sample‖^2) := by
      simp_rw [EuclideanSpace.real_norm_sq_eq]
      exact Finset.measurable_sum _ (fun l _=>(measurable_vectorMeanOverlap_component μ β t ht.le q l).pow_const 2)
    rw [integral_vectorMeasureSpinPathLaw_sample (n:=n) μ β t a ht.le _ hm]
    exact vector_free_support_norm_contact hn μ s hs hμ β t a hβ ht ha hmin q hq
  · simp_rw [vectorMeasureHessianMatrix_trace_square]
    change (∫p : VectorDisorderBrownianSample n×Configuration n,vectorMeasureHessianEnergy μ β t ht.le q p.1
      ∂vectorMeasureSpinPathLaw μ β t a ht.le)≤(n:ℝ)/((1-t)*β^2)
    rw [integral_vectorMeasureSpinPathLaw_sample (n:=n) μ β t a ht.le _
      (measurable_vectorMeasureHessianEnergy μ β t ht.le q)]
    exact vector_free_support_hessian_energy_bound hn μ s hs hμ β t a hβ ht ha hmin q hq

/-- The manuscript's complete contact proposition, including overlap zero,
the actual joint spin law, and the stated temperature and floor ranges. -/
theorem contact_proposition (hn : 0<n) (β : ℝ) (hβ : 0<β)
    (s : ℝ) (hs : s∈Ioc (0:ℝ) (1/2)) (t : ℝ) (ht : t∈Ico (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (hμ : μ∈scalarFloor s) :
    (∀q : Paper.Overlap,∀ᵐp ∂vectorMeasureSpinPathLaw (n:=n) μ β t s ht.2.le,
      (vectorMeasureSpinCovariance μ β t s ht.2.le q p.1).PosSemidef ∧
      (vectorMeasureHessianMatrix μ β t ht.2.le q p.1-
        Paper.parisiCDF μ q • vectorMeasureSpinCovariance μ β t s ht.2.le q p.1).PosSemidef ∧
      (vectorMeasureSpinCovariance μ β t s ht.2.le q p.1-
        vectorMeasureHessianMatrix μ β t ht.2.le q p.1).PosSemidef) ∧
    ((∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s) →
      ∀q∈(parisiFreeMeasure μ s).support,(q:ℝ)<1 ∧
      (∫p : VectorDisorderBrownianSample n×Configuration n,‖vectorMeasureSpinMean (n:=n) μ β t ht.2.le q p.1‖^2
        ∂vectorMeasureSpinPathLaw μ β t s ht.2.le)=(n:ℝ)*(q:ℝ) ∧
      (∫p : VectorDisorderBrownianSample n×Configuration n,Matrix.trace (vectorMeasureHessianMatrix μ β t ht.2.le q p.1*
        vectorMeasureHessianMatrix μ β t ht.2.le q p.1)
        ∂vectorMeasureSpinPathLaw μ β t s ht.2.le)≤(n:ℝ)/((1-t)*β^2)) := by
  refine ⟨fun q=>vectorMeasure_physical_matrix_order μ β t s hβ.ne' ht.2 q,?_⟩
  intro hmin q hq
  exact vector_free_support_physical_contact hn μ s ⟨hs.1.le,by linarith [hs.2]⟩ hμ
    β t s hβ.ne' ht.2 hs.1.le hmin q hq

end QuantitativePaper
