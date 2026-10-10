module
public import QuantitativePaper.VectorInterpolationSchedule
public import QuantitativePaper.CompletionCovariance

@[expose] public section

/-! Exact covariance directions of the actual finite interpolation. The
field direction has covariance v*N*R, and triangular disorder plus its genuine
independent common Gaussian has covariance beta^2*N*R^2/2. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators
namespace QuantitativePaper
open FourPapersCommon
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128

def vectorInterpolationFieldDirection (n : ℕ) (v : ℝ) :
    VectorInterpolationInput n →L[ℝ] FiniteStateField (Configuration n) :=
  Real.sqrt v • ((vectorSpinFieldEmbedding n).comp (vectorInterpolationFieldLinear n))

def vectorInterpolationDisorderDirection (n : ℕ) (β : ℝ) :
    VectorInterpolationInput n →L[ℝ] FiniteStateField (Configuration n) :=
  (vectorDisorderFieldEmbedding n β).comp (vectorInterpolationDisorderLinear n)

def vectorCompletedSpinCoefficient (n : ℕ) (β : ℝ) (σ : Configuration n) : Option (Edge n)→ℝ
  | none=>β/Real.sqrt 2
  | some e=>β/Real.sqrt (n:ℝ)*Paper.spinSign (σ e.val.1)*Paper.spinSign (σ e.val.2)

theorem vectorInterpolationFieldDirection_basis_inl (n : ℕ) (v : ℝ) (i : Fin n)
    (σ : Configuration n) :
    vectorInterpolationFieldDirection n v (EuclideanSpace.single (.inl i) 1) σ=
      Real.sqrt v*Paper.spinSign (σ i) := by
  simp [vectorInterpolationFieldDirection,vectorSpinFieldEmbedding,vectorInterpolationFieldLinear,
    vectorInterpolationField,fieldDot,EuclideanSpace.single_apply]

theorem vectorInterpolationFieldDirection_basis_inr (n : ℕ) (v : ℝ) (e : Option (Edge n))
    (σ : Configuration n) :
    vectorInterpolationFieldDirection n v (EuclideanSpace.single (.inr e) 1) σ=0 := by
  simp [vectorInterpolationFieldDirection,vectorSpinFieldEmbedding,vectorInterpolationFieldLinear,
    vectorInterpolationField,fieldDot,EuclideanSpace.single_apply]

theorem vectorInterpolationDisorderDirection_basis_inl (n : ℕ) (β : ℝ) (i : Fin n)
    (σ : Configuration n) :
    vectorInterpolationDisorderDirection n β (EuclideanSpace.single (.inl i) 1) σ=0 := by
  simp [vectorInterpolationDisorderDirection,vectorDisorderFieldEmbedding,vectorInterpolationDisorderLinear,
    vectorInterpolationDisorder,energyLinear,EuclideanSpace.single_apply]

theorem vectorInterpolationDisorderDirection_basis_inr (n : ℕ) (β : ℝ) (e : Option (Edge n))
    (σ : Configuration n) :
    vectorInterpolationDisorderDirection n β (EuclideanSpace.single (.inr e) 1) σ=
      vectorCompletedSpinCoefficient n β σ e := by
  cases e with
  | none=>
    simp [vectorInterpolationDisorderDirection,vectorDisorderFieldEmbedding,vectorInterpolationDisorderLinear,
      vectorInterpolationDisorder,energyLinear,EuclideanSpace.single_apply,vectorCompletedSpinCoefficient]
    ring
  | some e=>
    simp [vectorInterpolationDisorderDirection,vectorDisorderFieldEmbedding,vectorInterpolationDisorderLinear,
      vectorInterpolationDisorder,energyLinear,EuclideanSpace.single_apply,vectorCompletedSpinCoefficient]
    ring

theorem vectorCompletedSpinCoefficient_product (n : ℕ) (hn : 0<n) (β : ℝ)
    (σ τ : Configuration n) (e : Option (Edge n)) :
    vectorCompletedSpinCoefficient n β σ e*vectorCompletedSpinCoefficient n β τ e=
      Paper.physicalSKCoefficient n β σ e*Paper.physicalSKCoefficient n β τ e := by
  cases e <;> simp [vectorCompletedSpinCoefficient,Paper.physicalSKCoefficient,
    Paper.skCommonNoiseCoefficient,hn.ne'] <;> ring

theorem vectorInterpolationFieldDirection_spectral (n : ℕ) (v : ℝ) (hv : 0≤v)
    (σ τ : Configuration n) :
    finiteStateSpectralCovariance (vectorInterpolationFieldDirection n v) σ τ=
      v*∑i : Fin n,Paper.spinSign (σ i)*Paper.spinSign (τ i) := by
  unfold finiteStateSpectralCovariance
  rw [Fintype.sum_sum_type]
  simp_rw [vectorInterpolationFieldDirection_basis_inl,vectorInterpolationFieldDirection_basis_inr]
  simp only [mul_zero,Finset.sum_const_zero,add_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _=(Real.sqrt v)^2*(Paper.spinSign (σ i)*Paper.spinSign (τ i)) := by ring
    _=_ := by rw [Real.sq_sqrt hv]

theorem vectorInterpolationFieldDirection_spectral_overlap (n : ℕ) (hn : 0<n)
    (v : ℝ) (hv : 0≤v) (σ τ : Configuration n) :
    finiteStateSpectralCovariance (vectorInterpolationFieldDirection n v) σ τ=
      v*(n:ℝ)*overlap n σ τ := by
  rw [vectorInterpolationFieldDirection_spectral n v hv]
  have hnr : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  unfold overlap
  field_simp

theorem vectorInterpolationDisorderDirection_spectral (n : ℕ) (hn : 0<n)
    (β : ℝ) (σ τ : Configuration n) :
    finiteStateSpectralCovariance (vectorInterpolationDisorderDirection n β) σ τ=
      (n:ℝ)*β^2/2*overlap n σ τ^2 := by
  unfold finiteStateSpectralCovariance
  rw [Fintype.sum_sum_type]
  simp_rw [vectorInterpolationDisorderDirection_basis_inl,vectorInterpolationDisorderDirection_basis_inr]
  simp only [zero_mul,Finset.sum_const_zero,zero_add]
  simp_rw [vectorCompletedSpinCoefficient_product n hn β]
  exact Paper.physicalSKCoefficient_covariance n β σ τ

end QuantitativePaper
