module
public import QuantitativePaper.VectorSpinPosterior
public import QuantitativePaper.VectorPosteriorJets
public import QuantitativePaper.VectorOverlapScore
public import QuantitativeFollowup.FinitePosteriorBL

@[expose] public section

/-! Genuine Brascamp--Lieb for the actual finite vector posterior.
The density, probability normalization, coercivity, and potential jets are
proved for this model; the final overlap-score theorem supplies its actual
observable regularity as well. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets QuantitativeFollowup
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128

theorem iteratedFDeriv_normalizedPosteriorPotential {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E]
    (V : E → ℝ) (hV : ContDiff ℝ ∞ V) {j : ℕ} (hj : 1 ≤ j) (x : E) :
    iteratedFDeriv ℝ j (normalizedPosteriorPotential V) x=iteratedFDeriv ℝ j V x := by
  unfold normalizedPosteriorPotential
  change iteratedFDeriv ℝ j (V+(fun _ => Real.log (posteriorNormalizer V))) x=_
  have hc : ContDiff ℝ j (fun _ : E => Real.log (posteriorNormalizer V)) := contDiff_const
  rw [iteratedFDeriv_add_apply (hV.of_le (by simp)).contDiffAt
    hc.contDiffAt,
    iteratedFDeriv_const_of_ne (by omega),Pi.zero_apply,add_zero]

theorem vectorSpinPosterior_brascamp_lieb {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (hq : s.q 1=0) (ha : a ≤ s.m 1) (σ : Configuration n)
    (f : VectorGaussianSpace n k → ℝ) (hf : BoundedJets f) :
    variance f (vectorSpinPosteriorLaw s β t a σ) ≤
      ∫ x, inner ℝ (gradient f x)
        ((Ring.inverse (hessianOperator (vectorPosteriorPotential s β t a σ) x))
          (gradient f x)) ∂vectorSpinPosteriorLaw s β t a σ := by
  let V := vectorPosteriorPotential (n := n) s β t a σ
  let VN := normalizedPosteriorPotential V
  have hV : ContDiff ℝ ∞ V := contDiff_vectorPosteriorPotential s β t a σ
  haveI : Nonempty (VectorGaussianIndex n k) := ⟨Sum.inl none⟩
  haveI : IsProbabilityMeasure (posteriorDensityMeasure VN) :=
    vectorSpinPosteriorLaw_probability s β t a hq σ
  obtain ⟨A₁,hA₁,ha₁⟩ := exists_vectorPosteriorPotential_jet_bound s β t a σ (j := 3) (by omega)
  obtain ⟨A₂,hA₂,ha₂⟩ := exists_vectorPosteriorPotential_jet_bound s β t a σ (j := 4) (by omega)
  obtain ⟨Kf,hKf,hfb⟩ := hf.2 0
  obtain ⟨B₀,hB₀,hb₀⟩ := hf.2 1
  obtain ⟨B₁,hB₁,hb₁⟩ := hf.2 2
  obtain ⟨B₂,hB₂,hb₂⟩ := hf.2 3
  have hhc (x z : VectorGaussianSpace n k) :
      directionalHessian VN x z=directionalHessian V x z := by
    unfold directionalHessian
    have hd : fderiv ℝ VN=fderiv ℝ V := by
      funext y
      exact fderiv_add_const _
    rw [hd]
  have hh := posterior_brascamp_lieb_canonical_of_jet_bounds_finite VN f
    ((hV.add contDiff_const).of_le (by simp)) (hf.1.of_le (by simp))
    1 A₁ A₂ B₀ B₁ B₂ Kf (by norm_num)
    (fun x z => by rw [one_mul,hhc]; exact vectorPosteriorPotential_hessian_lower s β t a ha σ x z)
    (fun x => by simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using hfb x)
    (fun x => by rw [iteratedFDeriv_normalizedPosteriorPotential V hV (by omega)]; exact ha₁ x)
    (fun x => by rw [iteratedFDeriv_normalizedPosteriorPotential V hV (by omega)]; exact ha₂ x)
    hb₀ hb₁ hb₂
  simpa only [VN,V,hessianOperator_normalizedPosteriorPotential,
    vectorSpinPosteriorLaw,normalizedPosteriorMeasure] using hh

theorem vectorSpinPosterior_weightedOverlap_brascamp_lieb {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (hq : s.q 1=0) (ha : a ≤ s.m 1) (kernel : ℝ → ℝ)
    (σ : Configuration n) :
    variance (vectorEuclideanWeightedOverlapScore s β t a kernel σ)
      (vectorSpinPosteriorLaw s β t a σ) ≤
      ∫ x, inner ℝ (gradient (vectorEuclideanWeightedOverlapScore s β t a kernel σ) x)
        ((Ring.inverse (hessianOperator (vectorPosteriorPotential s β t a σ) x))
          (gradient (vectorEuclideanWeightedOverlapScore s β t a kernel σ) x))
        ∂vectorSpinPosteriorLaw s β t a σ :=
  vectorSpinPosterior_brascamp_lieb s β t a hq ha σ _
    (boundedJets_vectorEuclideanWeightedOverlapScore s β t a kernel σ)

end QuantitativePaper
