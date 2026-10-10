module
public import QuantitativeFollowup.AnisotropicSpinResponses
public import QuantitativeFollowup.AnisotropicFiniteCovariance
public import QuantitativePaper.VectorCovarianceQuadratic

@[expose] public section

/-! Genuine spin variances and pair-moment expansions for arbitrary
anisotropic posterior measures. The coordinate ordering never divides by a
Gaussian coupling scale. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology BigOperators
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128

def anisotropicOrderedCoupling (i j : Fin n) : AnisotropicCouplingIndex n :=
  ⟨(min i j,max i j),min_le_max⟩

theorem anisotropicOrderedCoupling_feature (i j : Fin n) (σ : Configuration n) :
    Paper.spinSign (σ (anisotropicOrderedCoupling i j).1.1)*
      Paper.spinSign (σ (anisotropicOrderedCoupling i j).1.2)=
        Paper.spinSign (σ i)*Paper.spinSign (σ j) := by
  by_cases h : i ≤ j
  · simp [anisotropicOrderedCoupling,min_eq_left h,max_eq_right h]
  · have h' : j ≤ i :=le_of_not_ge h
    simp [anisotropicOrderedCoupling,min_eq_right h',max_eq_left h',mul_comm]

theorem integrable_configuration_function (ρ : Measure (Configuration n)) [IsProbabilityMeasure ρ]
    (f : Configuration n→ℝ) : Integrable f ρ := by
  let C : ℝ:=∑σ : Configuration n,‖f σ‖
  exact (integrable_const C).mono' (measurable_of_finite f).aestronglyMeasurable
    (.of_forall fun σ=>Finset.single_le_sum (fun τ _=>norm_nonneg (f τ)) (Finset.mem_univ σ))

theorem configuration_variance_fieldDot (ρ : Measure (Configuration n)) [IsProbabilityMeasure ρ]
    (w : Field n) :
    variance (fun σ : Configuration n=>fieldDot w σ) ρ=
      ∑i : Fin n,∑j : Fin n,((∫σ,Paper.spinSign (σ i)*Paper.spinSign (σ j) ∂ρ)-
        (∫σ,Paper.spinSign (σ i) ∂ρ)*(∫σ,Paper.spinSign (σ j) ∂ρ))*w i*w j := by
  have hL : MemLp (fun σ : Configuration n=>fieldDot w σ) 2 ρ:=
    MemLp.of_bound (measurable_of_finite _).aestronglyMeasurable
      (∑σ : Configuration n,‖fieldDot w σ‖)
      (.of_forall fun σ=>Finset.single_le_sum (fun τ _=>norm_nonneg (fieldDot w τ))
        (Finset.mem_univ σ))
  rw [variance_eq_sub hL]
  simp only [Pi.pow_apply]
  have hs : (fun σ : Configuration n=>fieldDot w σ^2)=
      fun σ=>∑i : Fin n,∑j : Fin n,(w i*w j)*(Paper.spinSign (σ i)*Paper.spinSign (σ j)) :=
    funext (fieldDot_sq_eq_double_sum w)
  rw [hs,integral_finset_sum _ (fun i _=>integrable_configuration_function ρ _)]
  simp_rw [integral_finset_sum _ (fun j _=>integrable_configuration_function ρ _),integral_const_mul]
  have hm : (∫σ,fieldDot w σ ∂ρ)=∑i : Fin n,w i*(∫σ,Paper.spinSign (σ i) ∂ρ) := by
    unfold fieldDot
    rw [integral_finset_sum _ (fun i _=>integrable_configuration_function ρ _)]
    simp_rw [integral_const_mul]
  rw [hm,pow_two,Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  calc
    _=∑i : Fin n,∑j : Fin n,((w i*w j)*(∫σ,Paper.spinSign (σ i)*Paper.spinSign (σ j) ∂ρ)-
      (w i*(∫σ,Paper.spinSign (σ i) ∂ρ))*(w j*(∫σ,Paper.spinSign (σ j) ∂ρ))) := by
      simp only [Finset.sum_sub_distrib]
    _=_ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

def anisotropicTailSpinCovariance (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : Paper.Overlap) (P : AnisotropicParameter n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j=>anisotropicTailPairResponse D μ q P (anisotropicOrderedCoupling i j)-
    anisotropicMeasureTailMagnetization D μ q P i*anisotropicMeasureTailMagnetization D μ q P j

def anisotropicTailCovarianceQuadratic (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : Paper.Overlap) (P : AnisotropicParameter n) (w : Field n) : ℝ :=
  ∑i : Fin n,∑j : Fin n,anisotropicTailSpinCovariance D μ q P i j*w i*w j

theorem anisotropicSpinCovarianceEnergy_node_eq_pairExpansion (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : ℕ) (hi : i≤k+2) (P : AnisotropicParameter n) (w : Field n) :
    anisotropicSpinCovarianceEnergy D s (k+2-i) P w=
      ∑l : Fin n,∑j : Fin n,(anisotropicFiniteTailPairResponse D s (anisotropicSchemeNode s i hi) P
        (anisotropicOrderedCoupling l j)-anisotropicFiniteTailMagnetization D s
          (anisotropicSchemeNode s i hi) P l*anisotropicFiniteTailMagnetization D s
            (anisotropicSchemeNode s i hi) P j)*w l*w j := by
  rw [anisotropicSpinCovarianceEnergy,configuration_variance_fieldDot]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro j _
  rw [anisotropicFiniteTailPairResponse_node,anisotropicFiniteTailMagnetization_node]
  simp_rw [anisotropicOrderedCoupling_feature]
  rw [anisotropicMagnetization_eq_spin_mean,anisotropicMagnetization_eq_spin_mean]

end QuantitativeFollowup
