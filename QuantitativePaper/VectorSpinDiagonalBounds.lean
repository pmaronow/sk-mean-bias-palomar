module
public import QuantitativePaper.VectorSpinOffsetDirections

@[expose] public section

/-! Literal diagonal curvature bounds of the finite spin recursion, in both
log-partition and physical energy units. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators NNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets

theorem vectorSpinCovariance_eq_one_sub_square {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (p : Couplings n × ℝ) (j : ℕ) (x : Field n) (i : Fin n) :
    vectorObservableCovariance s β t p (fun σ=>Paper.spinSign (σ i)) j 0 x=
      1-(vectorMagnetization s β t p j x i)^2 := by
  have hs : (fun σ:Configuration n=>(Paper.spinSign (σ i))^2)=fun _=>1 := by
    funext σ
    cases σ i <;> norm_num [Paper.spinSign]
  unfold vectorObservableCovariance
  rw [hs,vectorConditionalMean_const]
  rfl

theorem vectorFieldHessian_diagonal_variance_bounds {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (p : Couplings n × ℝ) (j : ℕ) (x : Field n) (i : Fin n) :
    observableDepthMass s j*(1-(vectorMagnetization s β t p j x i)^2)≤
      (vectorFieldHessian s β t p j x (EuclideanSpace.single i 1)) i ∧
    (vectorFieldHessian s β t p j x (EuclideanSpace.single i 1)) i≤1 := by
  rw [vectorFieldHessian_diagonal_eq_secondResponse]
  have hh:=vectorObservableSecondResponse_covariance_bounds s β t p
    (fun σ=>Paper.spinSign (σ i)) 1 (fun σ=>by simp) j 0 x
  rw [vectorSpinCovariance_eq_one_sub_square] at hh
  exact ⟨hh.1,hh.2.trans (by nlinarith [sq_nonneg (vectorMagnetization s β t p j x i)])⟩

theorem vectorFieldHessian_diagonal_nonneg {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (p : Couplings n × ℝ) (j : ℕ) (x : Field n) (i : Fin n) :
    0≤(vectorFieldHessian s β t p j x (EuclideanSpace.single i 1)) i := by
  have hb:=vectorMagnetization_component_bound s β t p j x i
  have hs : (vectorMagnetization s β t p j x i)^2≤1 := by
    have hb' := abs_le.mp hb
    nlinarith
  exact (mul_nonneg (observableDepthMass_nonneg s j) (sub_nonneg.2 hs)).trans
    (vectorFieldHessian_diagonal_variance_bounds s β t p j x i).1

theorem vectorPhysicalHessian_diagonal_bounds {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (hβ:0≤β) (p : Couplings n × ℝ) (j : ℕ) (x : Field n) (i : Fin n) :
    (β*observableDepthMass s j)*(1-(vectorMagnetization s β t p j x i)^2)≤
      β*(vectorFieldHessian s β t p j x (EuclideanSpace.single i 1)) i ∧
    β*(vectorFieldHessian s β t p j x (EuclideanSpace.single i 1)) i≤β := by
  have hh:=vectorFieldHessian_diagonal_variance_bounds s β t p j x i
  constructor
  · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh.1 hβ
  · simpa only [mul_one] using mul_le_mul_of_nonneg_left hh.2 hβ

theorem vectorPhysicalHessian_one_sub_abs_le {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (hβ:0≤β) (p : Couplings n × ℝ) (j : ℕ) (x : Field n) (i : Fin n)
    (hm:1≤β*observableDepthMass s j) :
    1-|vectorMagnetization s β t p j x i|≤
      β*(vectorFieldHessian s β t p j x (EuclideanSpace.single i 1)) i := by
  have hb:=vectorMagnetization_component_bound s β t p j x i
  have hs : (vectorMagnetization s β t p j x i)^2≤1 := by
    have hb' := abs_le.mp hb
    nlinarith
  have hh:1-(vectorMagnetization s β t p j x i)^2≤
      (β*observableDepthMass s j)*(1-(vectorMagnetization s β t p j x i)^2):=by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hm (sub_nonneg.2 hs)
  apply le_trans _ (hh.trans (vectorPhysicalHessian_diagonal_bounds s β t hβ p j x i).1)
  nlinarith [sq_abs (vectorMagnetization s β t p j x i),abs_nonneg (vectorMagnetization s β t p j x i)]

end QuantitativePaper
