module
public import QuantitativePaper.VectorTailAllJets
public import QuantitativePaper.VectorMeasureGradient
public import FourPapersCommon.SmoothUniformLimit

@[expose] public section

/-! Genuine all-order spatial regularity of the arbitrary-measure potential.
Every positive jet is the actual uniform limit of finite dyadic jets, whose
bounds are independent of approximation depth. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ContDiff Topology
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem contDiff_vectorDyadicTailPotential (μ : Paper.ParisiMeasure) (β t : ℝ)
    (q : Paper.Overlap) (j : ℕ) (p : Couplings n × ℝ) :
    ContDiff ℝ ∞ (vectorDyadicTailPotential μ β t q j p) := by
  unfold vectorDyadicTailPotential
  rw [vectorTailRecursion_eq_clamped _ β t q q.property p le_rfl]
  exact contDiff_vectorRecursion_field _ β t p _

theorem norm_vectorDyadicTailPotential_jet_le_uniform (μ : Paper.ParisiMeasure) (β t : ℝ)
    (q : Paper.Overlap) (j : ℕ) (p : Couplings n × ℝ) (r : ℕ) (hr : 1 ≤ r) (x : Field n) :
    ‖iteratedFDeriv ℝ r (vectorDyadicTailPotential μ β t q j p) x‖ ≤ vectorSpatialJetBound n r := by
  exact norm_vectorTailRecursion_jet_le_uniform _ β t q q.property p _ le_rfl r hr x

theorem vectorMeasureTailPotential_spatialSmooth_and_jets (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t ≤ 1) (q : Paper.Overlap) (p : Couplings n × ℝ) :
    ContDiff ℝ ∞ (vectorMeasureTailPotential μ β t q p) ∧
      ∀r,TendstoUniformly (fun j => iteratedFDeriv ℝ r (vectorDyadicTailPotential μ β t q j p))
        (iteratedFDeriv ℝ r (vectorMeasureTailPotential μ β t q p)) atTop := by
  exact contDiff_uniformLimit_of_uniform_jet_bounds
    (fun j => vectorDyadicTailPotential μ β t q j p) (vectorMeasureTailPotential μ β t q p)
    (fun j => contDiff_vectorDyadicTailPotential μ β t q j p) (vectorSpatialJetBound n)
    (vectorSpatialJetBound_nonneg n)
    (fun r hr j x => norm_vectorDyadicTailPotential_jet_le_uniform μ β t q j p r (by omega) x)
    ((tendstoUniformly_vectorDyadicTailPotential μ β t ht).comp (fun x => (q,(p,x))))

theorem contDiff_vectorMeasureTailPotential (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t ≤ 1) (q : Paper.Overlap) (p : Couplings n × ℝ) :
    ContDiff ℝ ∞ (vectorMeasureTailPotential μ β t q p) :=
  (vectorMeasureTailPotential_spatialSmooth_and_jets μ β t ht q p).1

theorem tendstoUniformly_vectorDyadicTailPotential_jet (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t ≤ 1) (q : Paper.Overlap) (p : Couplings n × ℝ) (r : ℕ) :
    TendstoUniformly (fun j => iteratedFDeriv ℝ r (vectorDyadicTailPotential μ β t q j p))
      (iteratedFDeriv ℝ r (vectorMeasureTailPotential μ β t q p)) atTop :=
  (vectorMeasureTailPotential_spatialSmooth_and_jets μ β t ht q p).2 r

theorem norm_vectorMeasureTailPotential_jet_le_uniform (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t ≤ 1) (q : Paper.Overlap) (p : Couplings n × ℝ) (r : ℕ) (hr : 1 ≤ r) (x : Field n) :
    ‖iteratedFDeriv ℝ r (vectorMeasureTailPotential μ β t q p) x‖ ≤ vectorSpatialJetBound n r := by
  apply le_of_tendsto ((tendstoUniformly_vectorDyadicTailPotential_jet μ β t ht q p r).tendsto_at x).norm
  exact Eventually.of_forall (fun j => norm_vectorDyadicTailPotential_jet_le_uniform μ β t q j p r hr x)

def vectorMeasureHessian (μ : Paper.ParisiMeasure) (β t : ℝ) (q : Paper.Overlap)
    (p : Couplings n × ℝ) (x : Field n) : Field n →L[ℝ] Field n :=
  hessianOperator (vectorMeasureTailPotential μ β t q p) x

theorem hasFDerivAt_vectorMeasureGradient (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t ≤ 1) (q : Paper.Overlap) (p : Couplings n × ℝ) (x : Field n) :
    HasFDerivAt (vectorMeasureGradient μ β t q p) (vectorMeasureHessian μ β t q p x) x := by
  have he := funext (vectorMeasureGradient_eq_gradient μ β t ht q p)
  rw [he]
  exact hasFDerivAt_gradient_hessianOperator (vectorMeasureTailPotential μ β t q p)
    ((contDiff_vectorMeasureTailPotential μ β t ht q p).of_le (by simp)) x

theorem norm_vectorMeasureHessian_le (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t ≤ 1) (q : Paper.Overlap) (p : Couplings n × ℝ) (x : Field n) :
    ‖vectorMeasureHessian μ β t q p x‖ ≤ (n : ℝ) := by
  rw [←(hasFDerivAt_vectorMeasureGradient μ β t ht q p x).fderiv]
  simpa only [NNReal.coe_natCast] using norm_fderiv_le_of_lipschitz ℝ (x₀ := x)
    (vectorMeasureGradient_lipschitz μ β t ht q p)

theorem contDiff_vectorMeasureGradient (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t ≤ 1) (q : Paper.Overlap) (p : Couplings n × ℝ) :
    ContDiff ℝ ∞ (vectorMeasureGradient μ β t q p) := by
  rw [funext (vectorMeasureGradient_eq_gradient μ β t ht q p)]
  exact (InnerProductSpace.toDual ℝ (Field n)).symm.contDiff.comp
    ((contDiff_vectorMeasureTailPotential μ β t ht q p).fderiv_right (by simp))

end QuantitativePaper
