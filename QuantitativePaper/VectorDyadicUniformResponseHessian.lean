module
public import QuantitativePaper.VectorDyadicGridJetAgreement
public import QuantitativePaper.VectorDyadicStateConvergence
public import QuantitativePaper.VectorDyadicFixedHessianEnergy
public import QuantitativePaper.VectorMeasureHessianProcess

@[expose] public section

/-! Uniform convergence of the genuine grid-profile Hessian processes.
Both the field and the same-driver optimal diffusion vary with the grid. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ContDiff Topology
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem vectorFiniteTailHessian_lipschitz {k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (q : Paper.Overlap) (p : Couplings n × ℝ) :
    LipschitzWith (vectorSpatialJetBound n 3).toNNReal (vectorFiniteTailHessian s β t q p) := by
  let f := vectorTailRecursion (n := n) s β t q p (k+2)
  have hf : ContDiff ℝ 4 f := (contDiff_vectorTailRecursion_field s β t q p).of_le (by simp)
  apply lipschitzWith_of_nnnorm_fderiv_le ((contDiff_hessianOperator f hf).differentiable (by simp))
  intro x
  change ‖fderiv ℝ (hessianOperator f) x‖₊ ≤ _
  rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (vectorSpatialJetBound_nonneg n 3)]
  change ‖fderiv ℝ (hessianOperator f) x‖ ≤ _
  rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_hessianOperator f hf 1 (by norm_num)]
  exact norm_vectorTailRecursion_jet_le_uniform s β t q q.property p _ le_rfl 3 (by norm_num) x

theorem tendstoUniformly_vectorDyadicGridHessianProcess (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t ≤ 1) :
    TendstoUniformly (fun j (z : Paper.Overlap × VectorDisorderBrownianSample n) =>
      vectorMeasureHessianProcess (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β t ht z.1 z.2)
      (fun z => vectorMeasureHessianProcess μ β t ht z.1 z.2) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  let B := vectorSpatialJetBound n 3
  have hB : 0 ≤ B := vectorSpatialJetBound_nonneg n 3
  have he := (tendsto_vectorDyadicStateError n μ β t).eventually
    (gt_mem_nhds (show 0 < ε/(2*(B+1)) by positivity))
  have hj := (Metric.tendstoUniformly_iff.mp
    (tendstoUniformly_vectorDyadicTailPotential_jets (n := n) μ β t ht 2)) (ε/2) (by positivity)
  filter_upwards [he, hj] with j hstate hjet
  intro z
  let q := z.1
  let sample := z.2
  let X := vectorMeasureState μ β t ht (q : ℝ).toNNReal sample
  let Xj := vectorDyadicState μ β t ht j (q : ℝ).toNNReal sample
  let H := vectorFiniteTailHessian (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t q sample.1
  have hr : (q : ℝ).toNNReal ≤ 1 := by simpa using Real.toNNReal_le_toNNReal q.property.2
  have hpath : ‖Xj-X‖ ≤ vectorDyadicStateError n μ β t j := by
    simpa only [Xj, X, norm_sub_rev] using norm_vectorMeasureState_sub_dyadic_le μ β t ht j _ hr sample
  have hl : ‖H Xj-H X‖ ≤ B*‖Xj-X‖ := by
    simpa only [dist_eq_norm, B, Real.coe_toNNReal _ hB] using
      (vectorFiniteTailHessian_lipschitz _ β t q sample.1).dist_le_mul Xj X
  have hc : ‖H X-vectorMeasureHessian μ β t q sample.1 X‖ < ε/2 := by
    change ‖hessianOperator (vectorDyadicTailPotential μ β t q j sample.1) X-
      hessianOperator (vectorMeasureTailPotential μ β t q sample.1) X‖ < ε/2
    rw [norm_hessianOperator_sub_eq_secondJet _ _
      (contDiff_vectorDyadicTailPotential μ β t q j sample.1)
      (contDiff_vectorMeasureTailPotential μ β t ht q sample.1) X]
    simpa only [dist_eq_norm, norm_sub_rev] using hjet (q,(sample.1,X))
  have hb : B * (ε/(2*(B+1))) < ε/2 := by
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (show 0 < 2*(B+1) by positivity)).mpr
    nlinarith
  rw [dist_comm, dist_eq_norm]
  unfold vectorMeasureHessianProcess
  rw [vectorMeasureState_grid_eq_finite μ j β t ht _ hr sample,
    vectorMeasureHessian_grid_eq_finite μ j β t ht q sample.1]
  change ‖H Xj-vectorMeasureHessian μ β t q sample.1 X‖ < ε
  calc
    _ ≤ ‖H Xj-H X‖+‖H X-vectorMeasureHessian μ β t q sample.1 X‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ B*vectorDyadicStateError n μ β t j+‖H X-vectorMeasureHessian μ β t q sample.1 X‖ := by
      gcongr
      exact hl.trans (mul_le_mul_of_nonneg_left hpath hB)
    _ < ε := by
      have hm := mul_le_mul_of_nonneg_left hstate.le hB
      linarith

end QuantitativePaper
