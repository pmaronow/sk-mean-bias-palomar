module
public import QuantitativeFollowup.ThreeDescendantKernelMoments

@[expose] public section

/-! Deleted-coordinate covariance bounds for a genuine terminal-spin probability
measure. Positivity and the unit diagonal follow from the actual spin law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators
namespace QuantitativeFollowup
variable {N : ℕ}
set_option maxHeartbeats 1200000

private theorem spin_memLp (K : Measure (Configuration N)) [IsProbabilityMeasure K]
    (i : Fin N) : MemLp (fun σ : Configuration N=>Paper.spinSign (σ i)) 2 K :=
  MemLp.of_bound (measurable_of_finite _).aestronglyMeasurable 1
    (.of_forall fun σ=>by simp only [Real.norm_eq_abs,Paper.abs_spinSign,le_refl])

theorem cavitySpinKernelMean_abs_le_one (K : Measure (Configuration N)) [IsProbabilityMeasure K]
    (i : Fin N) : |cavitySpinKernelMean K i|≤1 := by
  have h := norm_integral_le_of_norm_le_const (μ:=K)
    (.of_forall fun σ : Configuration N=>show ‖Paper.spinSign (σ i)‖≤1 by
      simp only [Real.norm_eq_abs,Paper.abs_spinSign,le_refl])
  simpa only [cavitySpinKernelMean,Real.norm_eq_abs,probReal_univ,mul_one] using h

theorem cavitySpinKernelCovariance_eq_covariance (K : Measure (Configuration N)) [IsProbabilityMeasure K]
    (i j : Fin N) : cavitySpinKernelCovariance K i j=
      covariance (fun σ : Configuration N=>Paper.spinSign (σ i))
        (fun σ : Configuration N=>Paper.spinSign (σ j)) K := by
  rw [covariance_eq_sub (spin_memLp K i) (spin_memLp K j)]
  rfl

theorem cavitySpinKernelCovariance_diagonal (K : Measure (Configuration N)) [IsProbabilityMeasure K]
    (i : Fin N) : cavitySpinKernelCovariance K i i=1-(cavitySpinKernelMean K i)^2 := by
  have hs (σ : Configuration N) : Paper.spinSign (σ i)*Paper.spinSign (σ i)=1 := by
    rw [←pow_two,Paper.spinSign_sq]
  simp only [cavitySpinKernelCovariance,cavitySpinKernelSecond,hs,
    integral_const,probReal_univ,one_smul,pow_two]

def cavitySpinKernelEnergy (K : Measure (Configuration N)) (J : Finset (Fin N)) : ℝ :=
  variance (fun σ : Configuration N=>∑i∈J,cavitySpinKernelMean K i*Paper.spinSign (σ i)) K

theorem cavitySpinKernelEnergy_eq_covariance_sum (K : Measure (Configuration N)) [IsProbabilityMeasure K]
    (J : Finset (Fin N)) : cavitySpinKernelEnergy K J=
      ∑i∈J,∑j∈J,cavitySpinKernelCovariance K i j*cavitySpinKernelMean K i*cavitySpinKernelMean K j := by
  unfold cavitySpinKernelEnergy
  rw [variance_fun_sum' (fun i _=>(spin_memLp K i).const_mul (cavitySpinKernelMean K i))]
  simp_rw [covariance_const_mul_left,covariance_const_mul_right,
    ←cavitySpinKernelCovariance_eq_covariance]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem cavitySpinKernel_deleted_energy_le (K : Measure (Configuration N)) [IsProbabilityMeasure K]
    (i : Fin N) : cavitySpinKernelEnergy K (Finset.univ.erase i)≤
      2*cavitySpinKernelEnergy K Finset.univ+2 := by
  let X := fun σ : Configuration N=>∑j : Fin N,cavitySpinKernelMean K j*Paper.spinSign (σ j)
  let Y := fun σ : Configuration N=>cavitySpinKernelMean K i*Paper.spinSign (σ i)
  have hX : MemLp X 2 K := memLp_finsetSum _
    (fun j _=>(spin_memLp K j).const_mul (cavitySpinKernelMean K j))
  have hY : MemLp Y 2 K := (spin_memLp K i).const_mul (cavitySpinKernelMean K i)
  have hvY : variance Y K≤1 := by
    rw [variance_const_mul]
    have hv : variance (fun σ : Configuration N=>Paper.spinSign (σ i)) K=
        1-(cavitySpinKernelMean K i)^2 := by
      rw [←covariance_self (spin_memLp K i).aemeasurable,
        ←cavitySpinKernelCovariance_eq_covariance,cavitySpinKernelCovariance_diagonal]
    rw [hv]
    have hM := cavitySpinKernelMean_abs_le_one K i
    have hM2 := pow_le_one₀ (n:=2) (abs_nonneg (cavitySpinKernelMean K i)) hM
    rw [sq_abs] at hM2
    nlinarith [sq_nonneg ((cavitySpinKernelMean K i)^2)]
  have hplus := variance_nonneg (X+Y) K
  rw [variance_add hX hY] at hplus
  have hsub := variance_fun_sub hX hY
  have he : (fun σ : Configuration N=>∑j∈Finset.univ.erase i,
      cavitySpinKernelMean K j*Paper.spinSign (σ j))=fun σ=>X σ-Y σ := by
    funext σ
    have h := Finset.sum_erase_add (s:=(Finset.univ : Finset (Fin N)))
      (f:=fun j=>cavitySpinKernelMean K j*Paper.spinSign (σ j)) (Finset.mem_univ i)
    dsimp only [X,Y]
    linarith
  unfold cavitySpinKernelEnergy
  rw [he,hsub]
  change variance X K-2*covariance X Y K+variance Y K≤2*variance X K+2
  linarith

theorem cavitySpinKernel_deleted_trace_le (K : Measure (Configuration N)) [IsProbabilityMeasure K]
    (J : Finset (Fin N)) :
    (∑i∈J,∑j∈J,(cavitySpinKernelCovariance K i j)^2)≤
      ∑i : Fin N,∑j : Fin N,(cavitySpinKernelCovariance K i j)^2 := by
  calc
    _≤∑i∈J,∑j : Fin N,(cavitySpinKernelCovariance K i j)^2 :=
      Finset.sum_le_sum fun i _=>Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ J)
        (fun j _ _=>sq_nonneg _)
    _≤_ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ J)
      (fun i _ _=>Finset.sum_nonneg fun j _=>sq_nonneg _)

theorem cavitySpinKernel_pair_covariance_sum (K : Measure (Configuration N)) [IsProbabilityMeasure K]
    (J : Finset (Fin N)) :
    (∑i∈J,∑j∈J,cavitySpinKernelCovariance K i j*cavitySpinKernelSecond K i j)=
      (∑i∈J,∑j∈J,(cavitySpinKernelCovariance K i j)^2)+cavitySpinKernelEnergy K J := by
  rw [cavitySpinKernelEnergy_eq_covariance_sum]
  simp only [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  unfold cavitySpinKernelCovariance
  ring

theorem cavitySpinKernel_three_deleted_square_le (K : Measure (Configuration N)) [IsProbabilityMeasure K]
    (i : Fin N) :
    (∫z,(cavitySpinDifferencePairing (Finset.univ.erase i) z)^2 ∂(K.prod K).prod K)≤
      2*(∫z,(cavitySpinDifferencePairing Finset.univ z)^2 ∂(K.prod K).prod K)+4 := by
  rw [cavitySpinKernel_three_difference_square,cavitySpinKernel_three_difference_square,
    cavitySpinKernel_pair_covariance_sum,cavitySpinKernel_pair_covariance_sum]
  have ht := cavitySpinKernel_deleted_trace_le K (Finset.univ.erase i)
  have he := cavitySpinKernel_deleted_energy_le K i
  have h0 : 0≤∑j : Fin N,∑l : Fin N,(cavitySpinKernelCovariance K j l)^2 :=
    Finset.sum_nonneg fun j _=>Finset.sum_nonneg fun l _=>sq_nonneg _
  linarith

end QuantitativeFollowup
