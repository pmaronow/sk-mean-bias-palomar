module
public import QuantitativePaper.VectorDyadicGridLawAgreement
public import QuantitativePaper.VectorGridProfileMix
public import QuantitativePaper.VectorProfileRetainedPhysicalTrace
public import QuantitativePaper.ResponseModel

@[expose] public section

/-! Actual finite-cell response observables are exactly the physical
arbitrary-measure response observables for the common dyadic grid mix. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2500000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 300000
variable {n : ℕ}

theorem vectorProfileCellJointPotential_grid_mix (μ ν : Paper.ParisiMeasure) (j : ℕ)
    (β t θ : ℝ) (ht : t≤1) (hθ : θ∈Icc (0:ℝ) 1)
    (i : ℕ) (hi : i≤vectorDyadicIndex j+2) (q : Paper.Overlap)
    (hq : (q:ℝ)∈Icc ((Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q i)
      ((Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q (i+1))) (p : Couplings n×ℝ) :
    (fun x=>vectorProfileCellJointPotential (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
      (Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)) β t i ((q,θ,p),x))=
      vectorMeasureTailPotential (Paper.parisiGridMeasure (Paper.parisiMix μ ν θ) (vectorDyadicIndex j)) β t q p:=by
  rw [vectorMeasureTailPotential_grid_eq_finite (Paper.parisiMix μ ν θ) j β t ht q p,
    ←vector_grid_profile_scheme_eq_mix μ ν (vectorDyadicIndex j) θ hθ,
    ←vectorProfileTailRecursion_eq_scheme _ _ β t q θ hθ p (vectorDyadicIndex j+3)]
  funext x
  exact vectorProfilePhysicalCell_eq_tail _ _ β t i hi q θ hθ hq p x

theorem vectorProfile_grid_retained_physical_trace_expected (hn : 0<n)
    (μ ν : Paper.ParisiMeasure) (j : ℕ) (β t lam θ : ℝ) (ht : t≤1)
    (hθ : θ∈Icc (0:ℝ) 1) (i : ℕ) (hi : i≤vectorDyadicIndex j+2) (q : Paper.Overlap)
    (hq : (q:ℝ)∈Icc ((Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q i)
      ((Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q (i+1))) :
    vectorProfileRetainedExpectation (n:=n) (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
      (Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)) β t (lam/β) θ ht hθ
      (vectorProfileRetainedPhysicalTrace (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
        (Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)) β t i) q=
      (n:ℝ)*responseMeanHessian (n:=n)
        (Paper.parisiGridMeasure (Paper.parisiMix μ ν θ) (vectorDyadicIndex j)) β t lam ht q:=by
  have hq1 : (q:ℝ).toNNReal≤1:=by simpa only [Real.toNNReal_one] using Real.toNNReal_le_toNNReal q.property.2
  have heScheme:=vector_grid_profile_scheme_eq_mix μ ν (vectorDyadicIndex j) θ hθ
  unfold vectorProfileRetainedExpectation
  rw [heScheme]
  dsimp only
  rw [←vectorMeasureDisorderTilt_grid_eq_finite (Paper.parisiMix μ ν θ) j β t (lam/β) ht]
  simp_rw [←vectorMeasureState_grid_eq_finite (Paper.parisiMix μ ν θ) j β t ht (q:ℝ).toNNReal hq1]
  have he : (fun sample : VectorDisorderBrownianSample n=>
      vectorProfileRetainedPhysicalTrace (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
        (Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)) β t i q
        ((θ,sample.1),vectorMeasureState (Paper.parisiGridMeasure (Paper.parisiMix μ ν θ) (vectorDyadicIndex j)) β t ht (q:ℝ).toNNReal sample))=
      responseHessianTrace (n:=n) (Paper.parisiGridMeasure (Paper.parisiMix μ ν θ) (vectorDyadicIndex j)) β t ht q:=by
    funext sample
    unfold vectorProfileRetainedPhysicalTrace vectorProfileCellRawTrace
    rw [vectorProfileCellJointPotential_grid_mix μ ν j β t θ ht hθ i hi q hq sample.1]
    rfl
  rw [he]
  unfold responseMeanHessian
  have hn0 : (n:ℝ)≠0:=by exact_mod_cast hn.ne'
  field_simp [hn0]

end QuantitativePaper
