module
public import QuantitativePaper.VectorMeasureCovarianceTrace
public import FourPapersCommon.L2IntegralBounds
public import Mathlib.Algebra.Order.Chebyshev

@[expose] public section

/-! Literal energy-scale appendix response observables. The original
log-partition potential has field βy and is divided by β, so its physical
Hessian is β times the constructed log-partition Hessian. Both expectations
use the actual normalized disorder tilt λ/β and actual optimal diffusion. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Matrix
open scoped BigOperators NNReal
namespace QuantitativePaper
open FourPapersCommon
set_option maxHeartbeats 1200000
variable {n:ℕ}

def responsePoincareConstant : ℝ := Real.sqrt (Real.pi/2)
def responseCurvatureConstant (U:ℝ) : ℝ :=
  Real.exp (-16*responsePoincareConstant*max 1 U-2*(max 1 U)^2)/
    (2*(1+responsePoincareConstant))

theorem responsePoincareConstant_pos : 0<responsePoincareConstant := by
  exact Real.sqrt_pos.2 (by positivity)

theorem responseCurvatureConstant_pos (U:ℝ) : 0<responseCurvatureConstant U := by
  unfold responseCurvatureConstant
  exact div_pos (Real.exp_pos _) (by positivity [responsePoincareConstant_pos])

/-- Actual physical-scale trace at one constructed diffusion point. -/
def responseHessianTrace (μ:Paper.ParisiMeasure) (β t:ℝ) (ht:t≤1)
    (q:Paper.Overlap) (sample:VectorDisorderBrownianSample n) : ℝ :=
  β*Matrix.trace (vectorMeasureHessianMatrix μ β t ht q sample)

def responseMeanHessian (μ:Paper.ParisiMeasure) (β t lam:ℝ) (ht:t≤1)
    (q:Paper.Overlap) : ℝ :=
  (1/(n:ℝ))*∫sample,responseHessianTrace (n:=n) μ β t ht q sample
    ∂vectorMeasureDisorderTilt (n:=n) μ β t (lam/β)

def responseAveragedCurvature (μ:Paper.ParisiMeasure) (β t lam:ℝ) (ht:t≤1)
    (q:Paper.Overlap) : ℝ :=
  (β^2/(n:ℝ))*∫sample,vectorMeasureHessianEnergy (n:=n) μ β t ht q sample
    ∂vectorMeasureDisorderTilt (n:=n) μ β t (lam/β)

/-- The finite-dimensional trace inequality in the actual Euclidean field. -/
theorem vector_operator_trace_square_le (H:Field n→L[ℝ]Field n) :
    (∑i:Fin n,(H (EuclideanSpace.single i 1)) i)^2≤
      (n:ℝ)*vectorHessianHilbertSquare H := by
  have hs:=sq_sum_le_card_mul_sum_sq (s:=Finset.univ)
    (f:=fun i:Fin n=>(H (EuclideanSpace.single i 1)) i)
  simp only [Finset.card_univ,Fintype.card_fin] at hs
  apply hs.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
  unfold vectorHessianHilbertSquare
  apply Finset.sum_le_sum
  intro i _
  have h:=PiLp.norm_apply_le (H (EuclideanSpace.single i 1)) i
  rw [Real.norm_eq_abs] at h
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2

private theorem hessian_path_measurable (μ:Paper.ParisiMeasure) (β t:ℝ)
    (ht:t≤1) (q:Paper.Overlap) :
    Measurable (fun sample:VectorDisorderBrownianSample n=>
      vectorMeasureHessian μ β t q sample.1
        (vectorMeasureState μ β t ht (q:ℝ).toNNReal sample)) := by
  let insert : VectorDisorderBrownianSample n→Paper.Overlap×VectorParameter n :=
    fun sample=>(q,(sample.1,vectorMeasureState μ β t ht (q : ℝ).toNNReal sample))
  have hX : Measurable (fun sample : VectorDisorderBrownianSample n=>
      vectorMeasureState μ β t ht (q : ℝ).toNNReal sample) :=
    ((stronglyAdapted_vectorMeasureState (n:=n) μ β t ht (q : ℝ).toNNReal).measurable).mono
      ((vectorBrownianFiltration n).le _) le_rfl
  have hm : Measurable insert := measurable_const.prodMk (measurable_fst.prodMk hX)
  have hcomp := (continuous_vectorMeasureHessian (n:=n) μ β t ht).measurable.comp hm
  simpa only [insert,Function.comp_def] using hcomp

theorem measurable_responseHessianTrace (μ:Paper.ParisiMeasure) (β t:ℝ)
    (ht:t≤1) (q:Paper.Overlap) : Measurable (responseHessianTrace (n:=n) μ β t ht q) := by
  let H:=fun sample:VectorDisorderBrownianSample n=>
    vectorMeasureHessian μ β t q sample.1 (vectorMeasureState μ β t ht (q:ℝ).toNNReal sample)
  have hH:Measurable H:=hessian_path_measurable μ β t ht q
  unfold responseHessianTrace Matrix.trace Matrix.diag vectorMeasureHessianMatrix
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro i _
  exact ((EuclideanSpace.proj i).continuous.measurable).comp
    (((continuous_id.clm_apply continuous_const).measurable).comp hH)

theorem abs_responseHessianTrace_le (μ:Paper.ParisiMeasure) (β t:ℝ)
    (ht:t≤1) (q:Paper.Overlap) (sample:VectorDisorderBrownianSample n) :
    |responseHessianTrace μ β t ht q sample| ≤ |β| * (n:ℝ)^2 := by
  unfold responseHessianTrace Matrix.trace Matrix.diag vectorMeasureHessianMatrix
  rw [abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg β)
  calc
    |∑i:Fin n,(vectorMeasureHessian μ β t q sample.1
      (vectorMeasureState μ β t ht (q:ℝ).toNNReal sample) (EuclideanSpace.single i 1)) i|
      ≤∑i:Fin n,|(vectorMeasureHessian μ β t q sample.1
      (vectorMeasureState μ β t ht (q:ℝ).toNNReal sample) (EuclideanSpace.single i 1)) i| :=
        Finset.abs_sum_le_sum_abs _ _
    _≤∑_i:Fin n,(n:ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      have h1:=PiLp.norm_apply_le (vectorMeasureHessian μ β t q sample.1
        (vectorMeasureState μ β t ht (q:ℝ).toNNReal sample) (EuclideanSpace.single i 1)) i
      rw [Real.norm_eq_abs] at h1
      apply h1.trans
      simpa only [PiLp.norm_single,norm_one,mul_one] using
        ((vectorMeasureHessian μ β t q sample.1 _).le_opNorm (EuclideanSpace.single i 1)).trans
          (mul_le_mul_of_nonneg_right (norm_vectorMeasureHessian_le μ β t ht q sample.1 _)
            (norm_nonneg _))
    _=(n:ℝ)^2 := by simp [pow_two]

theorem memLp_responseHessianTrace (μ:Paper.ParisiMeasure) (β t lam:ℝ)
    (ht:t≤1) (q:Paper.Overlap) :
    MemLp (responseHessianTrace (n:=n) μ β t ht q) 2 (vectorMeasureDisorderTilt μ β t (lam/β)) := by
  letI:=vectorMeasureDisorderTilt_probability (n:=n) μ β t (lam/β) ht
  apply MemLp.of_bound (measurable_responseHessianTrace μ β t ht q).aestronglyMeasurable
    (|β| * (n:ℝ)^2)
  filter_upwards with sample
  simpa only [Real.norm_eq_abs] using abs_responseHessianTrace_le μ β t ht q sample

/-- Literal Jensen/trace step in the averaged-curvature proof, with actual
profile/process expectations and no supplied curvature conclusion. -/
theorem responseAveragedCurvature_ge_mean_square (hn:0<n) (μ:Paper.ParisiMeasure)
    (β t lam:ℝ) (ht:t≤1) (q:Paper.Overlap) :
    (responseMeanHessian (n:=n) μ β t lam ht q)^2≤
      responseAveragedCurvature (n:=n) μ β t lam ht q := by
  let P:=vectorMeasureDisorderTilt (n:=n) μ β t (lam/β)
  letI:=vectorMeasureDisorderTilt_probability (n:=n) μ β t (lam/β) ht
  have hJ:=integral_sq_le_mass_mul_integral_sq (responseHessianTrace (n:=n) μ β t ht q)
    (memLp_responseHessianTrace μ β t lam ht q)
  rw [probReal_univ,one_mul] at hJ
  have hHi:Integrable (fun sample:VectorDisorderBrownianSample n=>
      (responseHessianTrace μ β t ht q sample)^2) P := by
    exact (memLp_responseHessianTrace μ β t lam ht q).integrable_sq
  have hE:=integrable_vectorMeasureHessianEnergy (n:=n) μ β t (lam/β) ht q
  have hpoint (sample:VectorDisorderBrownianSample n) :
      (responseHessianTrace μ β t ht q sample)^2≤β^2*(n:ℝ)*
        vectorMeasureHessianEnergy μ β t ht q sample := by
    have hs:=vector_operator_trace_square_le (vectorMeasureHessian μ β t q sample.1
      (vectorMeasureState μ β t ht (q:ℝ).toNNReal sample))
    simpa only [responseHessianTrace,Matrix.trace,Matrix.diag,vectorMeasureHessianMatrix,
      mul_pow,mul_assoc,vectorMeasureHessianEnergy] using
      mul_le_mul_of_nonneg_left hs (sq_nonneg β)
  have hInt:=integral_mono hHi (hE.const_mul (β^2*(n:ℝ))) hpoint
  rw [integral_const_mul] at hInt
  have hnR:0<(n:ℝ):=by exact_mod_cast hn
  unfold responseMeanHessian responseAveragedCurvature
  change ((1/(n:ℝ))*(∫sample,responseHessianTrace μ β t ht q sample∂P))^2≤
    (β^2/(n:ℝ))*(∫sample,vectorMeasureHessianEnergy μ β t ht q sample∂P)
  rw [mul_pow]
  apply (mul_le_mul_of_nonneg_left (hJ.trans hInt) (sq_nonneg (1/(n:ℝ)))).trans_eq
  field_simp [ne_of_gt hnR]

end QuantitativePaper
