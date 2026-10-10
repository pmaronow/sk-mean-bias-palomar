module
public import QuantitativePaper.VectorMagnetizationGauge
public import QuantitativePaper.VectorOverlapScore
public import QuantitativePaper.VectorSpinDisintegration

@[expose] public section

/-! The actual manuscript overlap score is gauge-covariant. Its normalized
posterior mean therefore agrees in every spin slice. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128

theorem vectorEuclideanOverlapScore_gauge {n k : ℕ} (s : RSBScheme k)
    (η σ : Configuration n) (β t : ℝ) (i : ℕ) (z : VectorGaussianSpace n k) :
    vectorEuclideanOverlapScore s β t σ i (vectorGaussianGauge η z)=
      vectorEuclideanOverlapScore s β t (spinGauge η σ) i z := by
  have hn (x : Field n) : ‖fieldGauge η x‖=‖x‖ :=
    (coordinateSignEquiv _ (abs_spinSign η)).norm_map x
  simp only [vectorEuclideanOverlapScore,vectorEuclideanMagnetization_gauge,fieldDot_gauge,hn]

theorem vectorEuclideanWeightedOverlapScore_gauge {n k : ℕ} (s : RSBScheme k)
    (η σ : Configuration n) (β t a : ℝ) (kernel : ℝ → ℝ) (z : VectorGaussianSpace n k) :
    vectorEuclideanWeightedOverlapScore s β t a kernel σ (vectorGaussianGauge η z)=
      vectorEuclideanWeightedOverlapScore s β t a kernel (spinGauge η σ) z := by
  simp only [vectorEuclideanWeightedOverlapScore,vectorEuclideanOverlapScore_gauge]

theorem vectorEuclideanState_one_zero_field {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (hq : s.q 1=0) (z : VectorGaussianSpace n k) :
    (vectorEuclideanStateLinear s β t 1 z).2=0 := by
  rw [vectorEuclideanStateLinear_apply]
  have he : Fin.ofNat (k+3) 1=(0 : Fin (k+2)).succ := by ext;simp
  rw [he,vectorCoordinateHistory_next]
  have hi : (0 : Fin (k+2)).castSucc=(0 : Fin (k+3)) := rfl
  rw [hi,vectorCoordinateHistory_initial]
  simp [vectorCoordinateUpdate,vectorStateUpdate,fieldShift,hq,s.q_zero]

theorem vectorEuclideanMagnetization_one_zero {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (hq : s.q 1=0) (z : VectorGaussianSpace n k) :
    vectorEuclideanMagnetization s β t 1 z=0 := by
  unfold vectorEuclideanMagnetization
  rw [vectorEuclideanState_one_zero_field s β t hq]
  exact vectorMagnetization_zero_field _ _ _ _ _

theorem vectorEuclideanOverlapScore_one_zero {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (hq : s.q 1=0) (σ : Configuration n) (z : VectorGaussianSpace n k) :
    vectorEuclideanOverlapScore s β t σ 1 z=0 := by
  simp [vectorEuclideanOverlapScore,vectorEuclideanMagnetization_one_zero s β t hq,fieldDot]

theorem vectorEuclideanWeightedOverlapScore_posterior_means {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (kernel : ℝ → ℝ) (σ τ : Configuration n) :
    (∫z,vectorEuclideanWeightedOverlapScore s β t a kernel σ z ∂vectorSpinPosteriorLaw s β t a σ)=
      ∫z,vectorEuclideanWeightedOverlapScore s β t a kernel τ z ∂vectorSpinPosteriorLaw s β t a τ :=
  vectorSpinPosterior_invariant_means s β t a _
    (fun η ρ z => vectorEuclideanWeightedOverlapScore_gauge s η ρ β t a kernel z) σ τ

/-- The actual joint score has precisely the within-spin posterior variance;
the between-spin term vanishes by the proved spin gauge symmetry. -/
theorem variance_vectorEuclideanWeightedOverlapScore_eq_posterior {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (hq : s.q 1=0) (kernel : ℝ → ℝ) (σ : Configuration n) :
    variance (fun p : VectorGaussianSpace n k × Configuration n =>
        vectorEuclideanWeightedOverlapScore s β t a kernel p.2 p.1)
      (vectorEuclideanJointLaw s β t a)=
      variance (vectorEuclideanWeightedOverlapScore s β t a kernel σ)
        (vectorSpinPosteriorLaw s β t a σ) := by
  have hj (ρ : Configuration n) := boundedJets_vectorEuclideanWeightedOverlapScore s β t a kernel ρ
  choose B hB hBound using fun ρ => (hj ρ).2 0
  apply variance_vectorEuclideanJointLaw_invariant s β t a hq _
    (fun ρ => (hj ρ).1.continuous) (∑ρ : Configuration n,B ρ) _ _ σ
  · intro ρ z
    have hh : |vectorEuclideanWeightedOverlapScore s β t a kernel ρ z| ≤ B ρ := by
      simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using hBound ρ z
    exact hh.trans (Finset.single_le_sum (fun τ _ => hB τ) (Finset.mem_univ ρ))
  · exact fun η ρ z => vectorEuclideanWeightedOverlapScore_gauge s η ρ β t a kernel z

end QuantitativePaper
