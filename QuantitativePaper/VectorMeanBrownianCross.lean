module
public import QuantitativePaper.VectorBrownianLinearSums
public import QuantitativePaper.VectorMeasureHessianProcess
public import FRSB.MartingaleCrossSum

@[expose] public section

/-! Actual martingale conditioning removes all off-interval terms in the
cross expectation with an adapted vector Brownian linear sum. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon
open scoped NNReal ENNReal BigOperators
namespace QuantitativePaper
variable {n : ℕ}
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

theorem integral_vectorBrownianLinearSum_cross_martingale {m : ℕ}
    (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t ≤ 1)
    (M : Paper.Overlap → VectorDisorderBrownianSample n → ℝ)
    (hM : Martingale M (QuantitativeFollowup.vectorOverlapFiltration n) (vectorMeasureDisorderTilt μ β t a))
    (hM2 : ∀ q, MemLp (M q) 2 (vectorMeasureDisorderTilt μ β t a))
    (T : Fin (m+1) → Paper.Overlap) (hT : Monotone T)
    (H : Fin m → VectorDisorderBrownianSample n → (Field n →L[ℝ] ℝ))
    (hH : ∀ i, Measurable[vectorBrownianFiltration n (T i.castSucc : ℝ).toNNReal] (H i))
    (K : ℝ≥0) (hK : ∀ i sample, ‖H i sample‖ ≤ K) :
    (∫ sample, (M (T (Fin.last m)) sample-M (T 0) sample)*
      vectorBrownianLinearSum (fun i => (T i : ℝ).toNNReal) H sample ∂vectorMeasureDisorderTilt μ β t a) =
      ∑ i : Fin m, ∫ sample, (M (T i.succ) sample-M (T i.castSucc) sample)*
        H i sample (disorderVectorBrownianIncrement
          (T i.castSucc : ℝ).toNNReal (T i.succ : ℝ).toNNReal sample)
          ∂vectorMeasureDisorderTilt μ β t a := by
  have := vectorMeasureDisorderTilt_probability (n := n) μ β t a ht
  let P := vectorMeasureDisorderTilt (n := n) μ β t a
  let J : Fin n → Paper.Overlap → VectorDisorderBrownianSample n → ℝ := fun j q sample =>
    disorderVectorBrownian (q : ℝ).toNNReal sample j
  let C : Fin m → Fin n → VectorDisorderBrownianSample n → ℝ := fun i j sample =>
    H i sample (EuclideanSpace.single j 1)
  have hC (i : Fin m) (j : Fin n) :
      StronglyMeasurable[QuantitativeFollowup.vectorOverlapFiltration n (T i.castSucc)] (C i j) :=
    (((ContinuousLinearMap.apply ℝ ℝ) (EuclideanSpace.single j 1)).continuous.measurable.comp
      (hH i)).stronglyMeasurable
  have hCb (i : Fin m) (j : Fin n) (sample : VectorDisorderBrownianSample n) : ‖C i j sample‖ ≤ K := by
    exact ((H i sample).le_opNorm _).trans (by
      simpa only [PiLp.norm_single, norm_one, mul_one] using hK i sample)
  have hJ (j : Fin n) : Martingale (J j) (QuantitativeFollowup.vectorOverlapFiltration n) P :=
    martingale_vectorOverlapBrownian_coordinate μ β t a ht j
  have hJ2 (j : Fin n) (q : Paper.Overlap) : MemLp (J j q) 2 P :=
    memLp_vectorOverlapBrownian_coordinate μ β t a ht q j
  have hab (i : Fin m) : T i.castSucc ≤ T i.succ := hT (by
    simp only [Fin.le_def, Fin.val_castSucc, Fin.val_succ]; omega)
  have hpair (o z : Paper.Overlap) (i : Fin m) (j : Fin n) :
      Integrable (fun sample => (M z sample-M o sample)*
        (C i j sample*(J j (T i.succ) sample-J j (T i.castSucc) sample))) P :=
    memLp_one_iff_integrable.mp (((hM2 z).sub (hM2 o)).mul
      (FRSB.memLp_two_mul_bounded _ _ ((hC i j).mono
        ((QuantitativeFollowup.vectorOverlapFiltration n).le _)).aestronglyMeasurable
        ((hJ2 j _).sub (hJ2 j _)) K (hCb i j)))
  have hpoint (o z : Paper.Overlap) (i : Fin m) (sample : VectorDisorderBrownianSample n) :
      (M z sample-M o sample)*H i sample
        (disorderVectorBrownianIncrement (T i.castSucc : ℝ).toNNReal (T i.succ : ℝ).toNNReal sample) =
      ∑ j : Fin n, (M z sample-M o sample)*
        (C i j sample*(J j (T i.succ) sample-J j (T i.castSucc) sample)) := by
    rw [vector_linear_apply_eq_sum, Finset.mul_sum]
    rfl
  have hint (o z : Paper.Overlap) (i : Fin m) :
      Integrable (fun sample => (M z sample-M o sample)*H i sample
        (disorderVectorBrownianIncrement (T i.castSucc : ℝ).toNNReal (T i.succ : ℝ).toNNReal sample)) P := by
    simp_rw [hpoint o z i]
    exact integrable_finsetSum Finset.univ (fun j _ => hpair o z i j)
  change (∫ sample, (M (T (Fin.last m)) sample-M (T 0) sample)*
    (∑ i : Fin m, H i sample
      (disorderVectorBrownianIncrement (T i.castSucc : ℝ).toNNReal (T i.succ : ℝ).toNNReal sample)) ∂P) = _
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum Finset.univ (fun i _ => hint (T 0) (T (Fin.last m)) i)]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [hpoint]
  rw [integral_finsetSum Finset.univ (fun j _ => hpair (T 0) (T (Fin.last m)) i j),
    integral_finsetSum Finset.univ (fun j _ => hpair (T i.castSucc) (T i.succ) i j)]
  apply Finset.sum_congr rfl
  intro j _
  have hh := FRSB.terminal_martingale_cross_increment hM (hJ j) hM2 (hJ2 j)
    (hT (Fin.zero_le _)) (hab i) (hT (Fin.le_last _)) (C i j) (hC i j) K (hCb i j)
  convert hh using 1
  congr 1
  funext sample
  ring

end QuantitativePaper
