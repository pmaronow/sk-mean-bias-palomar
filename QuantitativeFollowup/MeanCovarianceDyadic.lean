module
public import QuantitativeFollowup.MeanCovarianceChain
public import QuantitativeFollowup.DyadicOverlap

@[expose] public section

/-! The genuine dyadic covariance-of-mean-increment estimate, including
zero-width intervals and the terminal piece. -/
noncomputable section
open MeasureTheory Set QuantitativePaper
open scoped NNReal ENNReal BigOperators
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def vectorMeanCovarianceIncrement (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t≤1)
    (p q : Paper.Overlap) : ℝ :=
  vectorDirectionCovariance (n:=n) μ β t a ht
    (fun sample=>vectorMeasureSpinMean μ β t ht q sample-vectorMeasureSpinMean μ β t ht p sample) q/(n:ℝ)^2

def dyadicMeanPiece (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (p q : Paper.Overlap) (hpq : p≤q) (K : ℕ) :
    Fin (K+1)→VectorDisorderBrownianSample n→Field n :=
  Fin.snoc (fun i : Fin K=>fun sample=>
    vectorMeasureSpinMean μ β t ht (dyadicOverlap p q hpq (i.val+1)) sample-
      vectorMeasureSpinMean μ β t ht (dyadicOverlap p q hpq i.val) sample)
    (fun sample=>vectorMeasureSpinMean μ β t ht q sample-
      vectorMeasureSpinMean μ β t ht (dyadicOverlap p q hpq K) sample)

theorem dyadicMeanPiece_sum (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (p q : Paper.Overlap) (hpq : p≤q) (K : ℕ) (sample : VectorDisorderBrownianSample n) :
    (∑i : Fin (K+1),dyadicMeanPiece μ β t ht p q hpq K i sample)=
      vectorMeasureSpinMean μ β t ht q sample-vectorMeasureSpinMean μ β t ht p sample := by
  have he := dyadicOverlap_increment_sum
    (fun k=>vectorMeasureSpinMean μ β t ht (dyadicOverlap p q hpq k) sample) K
  simp only [Fin.sum_univ_castSucc,dyadicMeanPiece,Fin.snoc_castSucc,Fin.snoc_last]
  rw [he,dyadicOverlap_zero]
  abel

theorem memLp_dyadicMeanPiece (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t≤1)
    (p q : Paper.Overlap) (hpq : p≤q) (K : ℕ) (i : Fin (K+1)) :
    MemLp (dyadicMeanPiece (n:=n) μ β t ht p q hpq K i) 2 (vectorMeasureDisorderTilt μ β t a) := by
  refine Fin.lastCases (motive:=fun j=>MemLp (dyadicMeanPiece (n:=n) μ β t ht p q hpq K j) 2
    (vectorMeasureDisorderTilt μ β t a)) ?_ ?_ i
  · simp only [dyadicMeanPiece,Fin.snoc_last]
    exact (memLp_vectorMeasureSpinMean μ β t a ht q).sub (memLp_vectorMeasureSpinMean μ β t a ht _)
  · simp only [dyadicMeanPiece,Fin.snoc_castSucc]
    intro j
    exact (memLp_vectorMeasureSpinMean μ β t a ht _).sub (memLp_vectorMeasureSpinMean μ β t a ht _)

theorem vector_mean_covariance_dyadic_bound (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s : ℝ) (hs : s∈Ioc (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (ha : 0≤a)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t a≤vectorMeasureFunctional n ν β t a)
    (p q : Paper.Overlap) (hpq : p≤q)
    (hq : q∈(parisiFreeMeasure μ s).support) (K : ℕ) :
    vectorMeanCovarianceIncrement (n:=n) μ β t a ht.le p q≤
      (K+1:ℝ)*(4*K/((n:ℝ)*((1-t)*β^2)*(Paper.parisiCDF μ (dyadicOverlap p q hpq 1))^2)+
        2*((q:ℝ)-p)*(1/2:ℝ)^K) := by
  by_cases hpqeq : p=q
  · subst q
    simp only [vectorMeanCovarianceIncrement,sub_self,vectorDirectionCovariance,
      vectorMeasureCovarianceQuadratic,PiLp.zero_apply,mul_zero,Finset.sum_const_zero,
      integral_zero,zero_div]
    have hc : 0≤1-t := by linarith
    positivity
  have hpqlt : p<q := lt_of_le_of_ne hpq hpqeq
  let c := (1-t)*β^2
  let A := Paper.parisiCDF μ (dyadicOverlap p q hpq 1)
  have hA : 0<A := hs.1.trans_le (scalarFloor_cdf_lower hμ (dyadicOverlap p q hpq 1).property.1)
  have hc : 0<c := mul_pos (sub_pos.mpr ht) (sq_pos_of_ne_zero hβ)
  have hca : c*A^2≠0 := ne_of_gt (mul_pos hc (sq_pos_of_pos hA))
  let b := dyadicMeanPiece (n:=n) μ β t ht.le p q hpq K
  have hsum := vectorDirectionCovariance_sum_le μ β t a hβ ht q b
    (memLp_dyadicMeanPiece μ β t a ht.le p q hpq K)
  have he : (fun sample=>∑i : Fin (K+1),b i sample)=
      fun sample=>vectorMeasureSpinMean μ β t ht.le q sample-vectorMeasureSpinMean μ β t ht.le p sample :=
    funext (dyadicMeanPiece_sum μ β t ht.le p q hpq K)
  rw [he] at hsum
  have hchain (i : Fin K) : vectorDirectionCovariance μ β t a ht.le (b i.castSucc) q≤4*(n:ℝ)/(c*A^2) := by
    simp only [b,dyadicMeanPiece,Fin.snoc_castSucc]
    apply vector_covariance_mean_chain_bound hn μ s ⟨hs.1.le,hs.2⟩ hμ β t a hβ ht ha hmin q hq
      (dyadicOverlap p q hpq 1) (dyadicOverlap p q hpq i.val) (dyadicOverlap p q hpq (i.val+1))
      (dyadicOverlap_middle_le p q hpq i.val)
      (monotone_dyadicOverlap p q hpq (by omega))
      (dyadicOverlap_lt p q hpqlt (i.val+1))
      (le_of_eq (dyadicOverlap_gap_double p q hpq i.val)) hA
  have hlast : vectorDirectionCovariance μ β t a ht.le (b (Fin.last K)) q≤
      2*(n:ℝ)^2*((q:ℝ)-p)*(1/2:ℝ)^K := by
    have hh := vector_covariance_mean_terminal_bound hn μ s ⟨hs.1.le,hs.2⟩ hμ β t a hβ ht ha hmin q hq
      (dyadicOverlap p q hpq K) (dyadicOverlap_le p q hpq K)
    simpa only [b,dyadicMeanPiece,Fin.snoc_last,dyadicOverlap_gap,mul_assoc] using hh
  have htot : vectorDirectionCovariance (n:=n) μ β t a ht.le
      (fun sample=>vectorMeasureSpinMean μ β t ht.le q sample-vectorMeasureSpinMean μ β t ht.le p sample) q≤
      (K+1:ℝ)*((K:ℝ)*(4*(n:ℝ)/(c*A^2))+2*(n:ℝ)^2*((q:ℝ)-p)*(1/2:ℝ)^K) := by
    apply hsum.trans
    simp only [Fintype.card_fin,Nat.cast_add,Nat.cast_one]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [Fin.sum_univ_castSucc]
    exact add_le_add (by simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      using Finset.sum_le_sum (s:=Finset.univ) (fun i _=>hchain i)) hlast
  have hnR : (n:ℝ)≠0 := ne_of_gt (Nat.cast_pos.mpr hn)
  unfold vectorMeanCovarianceIncrement
  apply (div_le_iff₀ (sq_pos_of_ne_zero hnR)).mpr
  apply htot.trans_eq
  have hne := hA.ne'
  dsimp only [A] at hne
  dsimp only [c,A]
  field_simp [hnR,hβ,sub_ne_zero.mpr ht.ne',hne]

end QuantitativeFollowup
