module
public import QuantitativeFollowup.FourDescendantNativeLaw

@[expose] public section

/-! Genuine three independent spin draws from a probability kernel.
The difference-square identity is derived by finite product Fubini. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1200000

def cavitySpinKernelMean (K : Measure (Configuration n)) (i : Fin n) : ℝ :=
  ∫σ,Paper.spinSign (σ i) ∂K

def cavitySpinKernelSecond (K : Measure (Configuration n)) (i j : Fin n) : ℝ :=
  ∫σ,Paper.spinSign (σ i)*Paper.spinSign (σ j) ∂K

def cavitySpinKernelCovariance (K : Measure (Configuration n)) (i j : Fin n) : ℝ :=
  cavitySpinKernelSecond K i j-cavitySpinKernelMean K i*cavitySpinKernelMean K j

private theorem finite_integrable {S : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (P : Measure S) [IsProbabilityMeasure P] (f : S→ℝ) :
    Integrable f P := by
  apply bounded_real_integrable f (measurable_of_finite f) (∑s,‖f s‖)
  intro s
  exact Finset.single_le_sum (fun t _=>norm_nonneg (f t)) (Finset.mem_univ s)

theorem cavitySpinKernel_difference_second (K : Measure (Configuration n)) [IsProbabilityMeasure K]
    (i j : Fin n) :
    (∫z : Configuration n×Configuration n,
      (Paper.spinSign (z.1 i)-Paper.spinSign (z.2 i))*
        (Paper.spinSign (z.1 j)-Paper.spinSign (z.2 j)) ∂K.prod K)=
      2*cavitySpinKernelCovariance K i j := by
  let A := fun z : Configuration n×Configuration n=>Paper.spinSign (z.1 i)*Paper.spinSign (z.1 j)
  let B := fun z : Configuration n×Configuration n=>Paper.spinSign (z.2 i)*Paper.spinSign (z.2 j)
  let C := fun z : Configuration n×Configuration n=>Paper.spinSign (z.1 i)*Paper.spinSign (z.2 j)
  let D := fun z : Configuration n×Configuration n=>Paper.spinSign (z.2 i)*Paper.spinSign (z.1 j)
  have he (z : Configuration n×Configuration n) :
      (Paper.spinSign (z.1 i)-Paper.spinSign (z.2 i))*(Paper.spinSign (z.1 j)-Paper.spinSign (z.2 j))=
      A z+B z-C z-D z := by dsimp only [A,B,C,D];ring
  simp_rw [he]
  rw [integral_sub (f:=fun z=>A z+B z-C z) (g:=D)
      (((finite_integrable (K.prod K) A).add (finite_integrable (K.prod K) B)).sub
        (finite_integrable (K.prod K) C)) (finite_integrable (K.prod K) D),
    integral_sub (f:=fun z=>A z+B z) (g:=C)
      ((finite_integrable (K.prod K) A).add (finite_integrable (K.prod K) B))
      (finite_integrable (K.prod K) C),
    integral_add (f:=A) (g:=B) (finite_integrable (K.prod K) A) (finite_integrable (K.prod K) B)]
  have hA : (∫z,A z ∂K.prod K)=cavitySpinKernelSecond K i j := by
    rw [integral_prod _ (finite_integrable (K.prod K) A)]
    simp only [A,integral_const,probReal_univ,one_smul,cavitySpinKernelSecond]
  have hB : (∫z,B z ∂K.prod K)=cavitySpinKernelSecond K i j := by
    rw [integral_prod _ (finite_integrable (K.prod K) B)]
    simp only [B,cavitySpinKernelSecond,integral_const,probReal_univ,one_smul]
  have hC : (∫z,C z ∂K.prod K)=cavitySpinKernelMean K i*cavitySpinKernelMean K j :=
    integral_prod_mul (fun σ : Configuration n=>Paper.spinSign (σ i))
      (fun σ : Configuration n=>Paper.spinSign (σ j))
  have hD : (∫z,D z ∂K.prod K)=cavitySpinKernelMean K j*cavitySpinKernelMean K i := by
    have he' (z : Configuration n×Configuration n) : D z=Paper.spinSign (z.1 j)*Paper.spinSign (z.2 i) := by
      dsimp only [D];ring
    simp_rw [he']
    exact integral_prod_mul (fun σ : Configuration n=>Paper.spinSign (σ j))
      (fun σ : Configuration n=>Paper.spinSign (σ i))
  rw [hA,hB,hC,hD]
  unfold cavitySpinKernelCovariance
  ring

def cavitySpinDifferencePairing (J : Finset (Fin n))
    (z : (Configuration n×Configuration n)×Configuration n) : ℝ :=
  ∑i∈J,(Paper.spinSign (z.1.1 i)-Paper.spinSign (z.1.2 i))*Paper.spinSign (z.2 i)

theorem cavitySpinKernel_three_difference_square (K : Measure (Configuration n)) [IsProbabilityMeasure K]
    (J : Finset (Fin n)) :
    (∫z,(cavitySpinDifferencePairing J z)^2 ∂(K.prod K).prod K)=
      2*(∑i∈J,∑j∈J,cavitySpinKernelCovariance K i j*cavitySpinKernelSecond K i j) := by
  have he (z : (Configuration n×Configuration n)×Configuration n) :
      (cavitySpinDifferencePairing J z)^2=
      ∑i∈J,∑j∈J,((Paper.spinSign (z.1.1 i)-Paper.spinSign (z.1.2 i))*
        (Paper.spinSign (z.1.1 j)-Paper.spinSign (z.1.2 j)))*
        (Paper.spinSign (z.2 i)*Paper.spinSign (z.2 j)) := by
    simp only [cavitySpinDifferencePairing,pow_two,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp_rw [he]
  rw [integral_finset_sum _ (fun i _=>integrable_finset_sum _ (fun j _=>finite_integrable _ _))]
  simp_rw [integral_finset_sum _ (fun j _=>finite_integrable _ _)]
  have hterm (i j : Fin n) :
      (∫z : (Configuration n×Configuration n)×Configuration n,
        ((Paper.spinSign (z.1.1 i)-Paper.spinSign (z.1.2 i))*
          (Paper.spinSign (z.1.1 j)-Paper.spinSign (z.1.2 j)))*
          (Paper.spinSign (z.2 i)*Paper.spinSign (z.2 j)) ∂(K.prod K).prod K)=
      2*(cavitySpinKernelCovariance K i j*cavitySpinKernelSecond K i j) := by
    rw [integral_prod_mul
      (f:=fun z : Configuration n×Configuration n=>(Paper.spinSign (z.1 i)-Paper.spinSign (z.2 i))*
        (Paper.spinSign (z.1 j)-Paper.spinSign (z.2 j)))
      (g:=fun σ : Configuration n=>Paper.spinSign (σ i)*Paper.spinSign (σ j)),
      cavitySpinKernel_difference_second]
    change (2*cavitySpinKernelCovariance K i j)*cavitySpinKernelSecond K i j= _
    ring
  simp_rw [hterm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact (Finset.mul_sum J _ _).symm

end QuantitativeFollowup
