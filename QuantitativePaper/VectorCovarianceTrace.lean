module
public import QuantitativePaper.VectorCovariancePairing
public import QuantitativePaper.VectorEnergyRegularity

@[expose] public section

/-! The actual conditional-spin covariance trace of the field Hessian. The
integrated identity uses the genuine finite-history law and its terminal
conditional means; measurability and bounds follow from the actual PDE jets. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128

def vectorFieldHessianMatrix {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (i : ℕ) (x : VectorState n) : Matrix (Fin n) (Fin n) ℝ := fun l j =>
  (vectorFieldHessian s β t x.1 (k+2-i) x.2 (EuclideanSpace.single j 1)) l

theorem euclidean_clm_quadratic_eq_sum {n : ℕ} (H : Field n →L[ℝ] Field n) (w : Field n) :
    inner ℝ w (H w)=∑l : Fin n,∑j : Fin n,
      (H (EuclideanSpace.single j 1)) l*w l*w j := by
  classical
  have hw : w=∑j : Fin n,w j • EuclideanSpace.single j 1 := by
    ext l
    simp [Pi.single_apply]
  have hHw (l : Fin n) : (H w) l=∑j : Fin n,(H (EuclideanSpace.single j 1)) l*w j := by
    conv_lhs => rw [hw]
    rw [map_sum]
    simp only [WithLp.ofLp_sum,Finset.sum_apply,map_smul,PiLp.smul_apply,smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro l _
  simp only [RCLike.inner_apply]
  rw [hHw,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  simp only [starRingEnd_apply,star_trivial]
  ring

theorem vectorSpinHessianEnergy_eq_covariance_sum {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (i : ℕ) (σ : Configuration n) (x : VectorState n) :
    vectorSpinHessianEnergy s β t (k+2-i) σ x=
      ∑l : Fin n,∑j : Fin n,vectorFieldHessianMatrix s β t i x l j*
        (Paper.spinSign (σ l)-vectorMagnetization s β t x.1 (k+2-i) x.2 l)*
        (Paper.spinSign (σ j)-vectorMagnetization s β t x.1 (k+2-i) x.2 j) := by
  simpa only [vectorSpinHessianEnergy,vectorFieldHessianMatrix,PiLp.sub_apply,
    spinVector,WithLp.ofLp_toLp] using
    euclidean_clm_quadratic_eq_sum (vectorFieldHessian s β t x.1 (k+2-i) x.2)
      (spinVector σ-vectorMagnetization s β t x.1 (k+2-i) x.2)

theorem matrix_trace_mul_vectorSpinCovariance {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (i : ℕ) (x : VectorState n) (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.trace (A*vectorSpinCovariance s β t i x)=
      ∑l : Fin n,∑j : Fin n,A l j*vectorSpinCovariance s β t i x l j := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro j _
  rw [vectorSpinCovariance_symmetric s β t i x j l]

theorem integral_vectorSpinHessianEnergy_eq_trace {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (i : ℕ) (hi : i≤k+2) :
    (∫p : VectorGaussianSpace n k × Configuration n,
      vectorSpinHessianEnergy s β t (k+2-i) p.2 (vectorEuclideanStateLinear s β t i p.1)
      ∂vectorEuclideanJointLaw s β t a)=
      ∫p : VectorGaussianSpace n k × Configuration n,
        Matrix.trace (vectorFieldHessianMatrix s β t i (vectorEuclideanStateLinear s β t i p.1)*
        vectorSpinCovariance s β t i (vectorEuclideanStateLinear s β t i p.1))
      ∂vectorEuclideanJointLaw s β t a := by
  let P := vectorEuclideanJointLaw (n := n) s β t a
  let X := fun p : VectorGaussianSpace n k × Configuration n => vectorEuclideanStateLinear s β t i p.1
  have hmX : Measurable X := by dsimp [X];fun_prop
  obtain ⟨K,hK,hBound⟩ := exists_vectorFieldHessian_component_bound (n := n) s β t (k+2-i)
  have hmA (l j : Fin n) : Measurable (fun x : VectorState n => vectorFieldHessianMatrix s β t i x l j) :=
    (continuous_vectorFieldHessian_component s β t (k+2-i) j l).measurable
  have hbA (x : VectorState n) (l j : Fin n) : |vectorFieldHessianMatrix s β t i x l j|≤K :=
    hBound x j l
  have hmM (l : Fin n) : Measurable (fun x : VectorState n => vectorMagnetization s β t x.1 (k+2-i) x.2 l) :=
    (boundedJets_vectorMagnetization_component s β t (k+2-i) l).1.continuous.measurable
  let f := fun (l j : Fin n) (p : VectorGaussianSpace n k × Configuration n) =>
    vectorFieldHessianMatrix s β t i (X p) l j*
      (Paper.spinSign (p.2 l)-vectorMagnetization s β t (X p).1 (k+2-i) (X p).2 l)*
      (Paper.spinSign (p.2 j)-vectorMagnetization s β t (X p).1 (k+2-i) (X p).2 j)
  let g := fun (l j : Fin n) (p : VectorGaussianSpace n k × Configuration n) =>
    vectorFieldHessianMatrix s β t i (X p) l j*vectorSpinCovariance s β t i (X p) l j
  have hfi (l j : Fin n) : Integrable (f l j) P := by
    refine integrable_vectorEuclidean_bounded s β t a _ ?_ (K*2*2) ?_
    · dsimp [f]
      exact ((hmA l j).comp hmX).mul
        (((measurable_of_finite (fun σ : Configuration n => Paper.spinSign (σ l))).comp measurable_snd).sub
          ((hmM l).comp hmX)) |>.mul
        (((measurable_of_finite (fun σ : Configuration n => Paper.spinSign (σ j))).comp measurable_snd).sub
          ((hmM j).comp hmX))
    · intro p
      dsimp [f]
      rw [abs_mul,abs_mul]
      exact mul_le_mul (mul_le_mul (hbA _ l j) (abs_vectorSpinResidual_le s β t i (X p) p.2 l)
        (abs_nonneg _) hK) (abs_vectorSpinResidual_le s β t i (X p) p.2 j) (abs_nonneg _) (by positivity)
  have hgi (l j : Fin n) : Integrable (g l j) P := by
    apply integrable_vectorEuclidean_bounded s β t a _
      (((hmA l j).comp hmX).mul ((measurable_vectorSpinCovariance_component s β t i l j).comp hmX)) (K*2)
    intro p
    dsimp [g]
    rw [abs_mul]
    exact mul_le_mul (hbA _ l j) (abs_vectorSpinCovariance_component_le s β t i (X p) l j)
      (abs_nonneg _) hK
  have he (l j : Fin n) : (∫p,f l j p ∂P)=∫p,g l j p ∂P := by
    simpa only [f,g,X,vectorEuclideanMagnetization] using
      integral_vector_spin_covariance_pairing s β t a i hi l j
        (fun x => vectorFieldHessianMatrix s β t i x l j) (hmA l j) K (fun x => hbA x l j)
  calc
    _ = ∫p,∑l : Fin n,∑j : Fin n,f l j p ∂P := by
      apply integral_congr_ae
      exact .of_forall fun p => vectorSpinHessianEnergy_eq_covariance_sum s β t i p.2 (X p)
    _ = ∑l : Fin n,∑j : Fin n,∫p,f l j p ∂P := by
      rw [integral_finsetSum _ (fun l _ => integrable_finsetSum _ (fun j _ => hfi l j))]
      apply Finset.sum_congr rfl
      intro l _
      exact integral_finsetSum _ (fun j _ => hfi l j)
    _ = ∑l : Fin n,∑j : Fin n,∫p,g l j p ∂P := by
      apply Finset.sum_congr rfl
      intro l _
      exact Finset.sum_congr rfl fun j _ => he l j
    _ = ∫p,∑l : Fin n,∑j : Fin n,g l j p ∂P := by
      rw [integral_finsetSum _ (fun l _ => integrable_finsetSum _ (fun j _ => hgi l j))]
      apply Finset.sum_congr rfl
      intro l _
      exact (integral_finsetSum _ (fun j _ => hgi l j)).symm
    _ = _ := by
      apply integral_congr_ae
      exact .of_forall fun p => (matrix_trace_mul_vectorSpinCovariance s β t i (X p) _).symm

end QuantitativePaper
