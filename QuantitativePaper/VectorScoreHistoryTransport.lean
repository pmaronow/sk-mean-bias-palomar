module
public import QuantitativePaper.VectorFiniteMarkedTransport
public import QuantitativePaper.VectorWeightedOverlapScore
public import QuantitativePaper.VectorNodeGradient
public import QuantitativePaper.VectorEnergyRegularity

@[expose] public section

/-! Exact score observables on the retained finite history.  The actual
diffusion/spin law and the Gaussian posterior give the same weighted score
variance; every weight is an actual free Stieltjes mass. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon
open scoped BigOperators NNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets QuantitativeFollowup
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

def vectorHistoryScore (s : RSBScheme k) (β t : ℝ) (i : ℕ)
    (p : FiniteHistory (VectorState n) (k+2)×Configuration n) : ℝ :=
  normalizedSpinScore (vectorMagnetization s β t (p.1 (Fin.ofNat (k+3) i)).1
    (k+2-i) (p.1 (Fin.ofNat (k+3) i)).2) p.2

def vectorHistoryWeightedScore (s : RSBScheme k) (β t a : ℝ) (κ : Paper.Overlap→ℝ)
    (p : FiniteHistory (VectorState n) (k+2)×Configuration n) : ℝ :=
  ∑i,vectorPosteriorFeatureWeight s a i*κ (vectorProfileAtom s i)*
    vectorHistoryScore s β t (vectorPosteriorFeatureTime i) p

theorem measurable_vectorHistoryScore (s : RSBScheme k) (β t : ℝ) (i : ℕ) :
    Measurable (vectorHistoryScore (n:=n) s β t i) := by
  apply measurable_from_prod_countable_left
  intro σ
  exact ((continuous_normalizedSpinScore σ).comp
    ((contDiff_vectorMagnetization_joint s β t (k+2-i)).continuous.comp
      (continuous_apply (Fin.ofNat (k+3) i)))).measurable

theorem measurable_vectorHistoryWeightedScore (s : RSBScheme k) (β t a : ℝ)
    (κ : Paper.Overlap→ℝ) : Measurable (vectorHistoryWeightedScore (n:=n) s β t a κ) := by
  classical
  exact Finset.measurable_sum _ fun i _=>
    measurable_const.mul (measurable_vectorHistoryScore s β t (vectorPosteriorFeatureTime i))

theorem vectorHistoryScore_euclidean (s : RSBScheme k) (β t : ℝ) (i : ℕ)
    (p : VectorGaussianSpace n k×Configuration n) :
    vectorHistoryScore s β t i (vectorEuclideanJointMap s β t p)=
      vectorEuclideanOverlapScore s β t p.2 i p.1 := by
  rw [vectorEuclideanOverlapScore_eq_normalized]
  unfold vectorHistoryScore vectorEuclideanMagnetization
  rw [vectorEuclideanStateLinear_apply]
  rfl

theorem vectorHistoryWeightedScore_euclidean (s : RSBScheme k) (β t a : ℝ)
    (κ : Paper.Overlap→ℝ) (p : VectorGaussianSpace n k×Configuration n) :
    vectorHistoryWeightedScore s β t a κ (vectorEuclideanJointMap s β t p)=
      vectorEuclideanWeightedOverlapScore s β t a (fun q=>κ (projIcc (0 : ℝ) 1 zero_le_one q)) p.2 p.1 := by
  classical
  unfold vectorHistoryWeightedScore vectorEuclideanWeightedOverlapScore
  simp_rw [vectorHistoryScore_euclidean]
  rw [Fintype.sum_option]
  simp only [vectorPosteriorFeatureWeight,vectorPosteriorFeatureTime,vectorProfileAtom]
  have hp (i : ℕ) (hi : i≤k+2) :
      projIcc (0 : ℝ) 1 zero_le_one (s.q i)=⟨s.q i,s.q_nonneg hi,s.q_le_one hi⟩ :=
    projIcc_of_mem zero_le_one ⟨s.q_nonneg hi,s.q_le_one hi⟩
  rw [hp 1 (by omega)]
  congr 1
  rw [←Fin.sum_univ_eq_sum_range (fun i : ℕ =>
    (s.m (i+2)-s.m (i+1))*κ (projIcc (0 : ℝ) 1 zero_le_one (s.q (i+2)))*
      vectorEuclideanOverlapScore s β t p.2 (i+2) p.1)]
  apply Finset.sum_congr rfl
  intro i _
  rw [hp (i+2) (by omega)]

theorem variance_vectorHistoryWeightedScore_transport (s : RSBScheme k) (β t a : ℝ)
    (hβ : β≠0) (ht : t<1) (κ : Paper.Overlap→ℝ) :
    variance (fun p=>vectorHistoryWeightedScore s β t a κ
      (vectorFiniteHistory s β t ht.le (k+2) p.1,p.2))
      (vectorFiniteSpinPathLaw (n:=n) s β t a ht.le)=
    variance (fun p : VectorGaussianSpace n k×Configuration n=>
      vectorEuclideanWeightedOverlapScore s β t a (fun q=>κ (projIcc (0 : ℝ) 1 zero_le_one q)) p.2 p.1)
      (vectorEuclideanJointLaw s β t a) := by
  rw [variance_vectorFiniteSpinPathLaw_history s β t a hβ ht _
    (measurable_vectorHistoryWeightedScore s β t a κ),
    ←variance_vectorEuclideanJointLaw_history s β t a _
      (measurable_vectorHistoryWeightedScore s β t a κ)]
  congr 1
  funext p
  exact vectorHistoryWeightedScore_euclidean s β t a κ p

theorem vectorHistoryScore_finite (s : RSBScheme k) (β t : ℝ) (ht : t≤1)
    (i : ℕ) (hi : i≤k+2) (p : VectorDisorderBrownianSample n×Configuration n) :
    vectorHistoryScore s β t i (vectorFiniteHistory s β t ht (k+2) p.1,p.2)=
      normalizedSpinScore (vectorFiniteTailGradient s β t
        ⟨s.q i,s.q_nonneg hi,s.q_le_one hi⟩ p.1.1
        (vectorFiniteState s β t ht (s.q i).toNNReal p.1)) p.2 := by
  rw [vectorFiniteTailGradient_at_node s β t i hi]
  unfold vectorHistoryScore vectorFiniteHistory historySample vectorFiniteJointState
  have he : (Fin.ofNat (k+3) i).val=i := by
    simp only [Fin.ofNat_eq_cast,Nat.cast_add,Nat.cast_ofNat,Fin.val_natCast]
    exact Nat.mod_eq_of_lt (by omega)
  simp only [he]

end QuantitativePaper
