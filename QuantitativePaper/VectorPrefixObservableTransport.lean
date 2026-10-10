module
public import QuantitativePaper.VectorSiteCurvatureAverage
public import QuantitativePaper.VectorFiniteTiltedPathLaw

@[expose] public section

/-! Actual bounded observations under the normalized Gaussian prefix are
transported to the constructed finite tilted diffusion, retaining its
initial disorder and entire chronological past. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1800000

theorem integral_vectorPrefixEuclideanLaw_terminal {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (N : ℕ) (hN : N ≤ k+2) (f : VectorState n→ℝ)
    (hf : Measurable f) (K : ℝ) (hK : ∀x,|f x| ≤ K) :
    (∫z,f (vectorPrefixEuclideanHistory s β t N z (Fin.last N))
      ∂vectorPrefixEuclideanLaw s β t a N)=
      ∫h,f (historyObservation (k+2) N h) ∂vectorFieldHistoryLaw s β t a := by
  have he := integral_vectorPrefixGaussianLaw_terminal s β t a N hN f hf K hK
  rw [←vectorPrefixEuclideanLaw_map s β t a N,
    integral_map (f:=fun p : VectorPrefixCoordinates n N=>f (vectorPrefixHistory s β t N p (Fin.last N)))
      (vectorPrefixEuclideanCoordinates n N).measurable.aemeasurable
      (hf.comp ((measurable_pi_apply (Fin.last N)).comp
        (measurable_vectorPrefixHistory s β t N))).aestronglyMeasurable] at he
  simp only [←vectorPrefixEuclideanHistory_apply] at he
  exact he.symm

theorem integral_vectorPrefixEuclideanLaw_finiteState {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (hβ : β ≠ 0) (ht : t < 1) (N : ℕ) (hN : N ≤ k+2)
    (f : VectorState n→ℝ) (hf : Measurable f) (K : ℝ) (hK : ∀x,|f x| ≤ K) :
    (∫z,f (vectorPrefixEuclideanHistory s β t N z (Fin.last N))
      ∂vectorPrefixEuclideanLaw s β t a N)=
      ∫sample,f (vectorFiniteJointState s β t ht.le (s.q N).toNNReal sample)
        ∂vectorFiniteDisorderTilt s β t a := by
  rw [integral_vectorPrefixEuclideanLaw_terminal s β t a N hN f hf K hK,
    ←vectorFinite_tilted_full_history_law s β t a hβ ht,
    integral_map (f:=fun h : FiniteHistory (VectorState n) (k+2)=>f (historyObservation (k+2) N h))
      (measurable_vectorFiniteHistory s β t ht.le (k+2)).aemeasurable
      (hf.comp (measurable_historyObservation (k+2) N)).aestronglyMeasurable]
  congr 1
  funext sample
  congr 1
  simp [historyObservation,vectorFiniteHistory,historySample,Nat.mod_eq_of_lt (by omega : N < k+2+1)]

end QuantitativePaper
