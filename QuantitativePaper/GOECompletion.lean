module
public import QuantitativePaper.Completion
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.LinearAlgebra.Matrix.Trace

public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

public import Mathlib.Probability.Distributions.Gaussian.Fernique

@[expose] public section

/-! Literal finite GOE coordinates, half-trace Gaussian completion, and the
pushforward to the concrete triangular model with its independent common noise. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal
namespace QuantitativePaper

abbrev Diagonals (n : ℕ) := Fin n → ℝ
def diagonalLaw (n : ℕ) : Measure (Diagonals n) :=
  Measure.pi (fun _ : Fin n => gaussianReal 0 1)
abbrev GOEDisorder (n : ℕ) := Couplings n × Diagonals n
def goeLaw (n : ℕ) : Measure (GOEDisorder n) := (couplingLaw n).prod (diagonalLaw n)
def diagonalSum (n : ℕ) (z : Diagonals n) : ℝ := ∑ i,z i
def goeDiagonalNoise (n : ℕ) (z : Diagonals n) : ℝ :=
  (1/Real.sqrt (2*(n : ℝ)))*diagonalSum n z

def goeMatrix (n : ℕ) (p : GOEDisorder n) : Matrix (Fin n) (Fin n) ℝ := fun i j =>
  (∑ e : Edge n, (p.1 e/Real.sqrt (n : ℝ))*
    ((if i = e.val.1 then 1 else 0)*(if j = e.val.2 then 1 else 0)+
     (if i = e.val.2 then 1 else 0)*(if j = e.val.1 then 1 else 0)))+
  (if i = j then Real.sqrt (2/(n : ℝ))*p.2 i else 0)

instance diagonalLaw_probability (n : ℕ) : IsProbabilityMeasure (diagonalLaw n) := by
  unfold diagonalLaw
  infer_instance
instance goeLaw_probability (n : ℕ) : IsProbabilityMeasure (goeLaw n) := by
  unfold goeLaw
  infer_instance

theorem diagonalCoordinate_law (n : ℕ) (i : Fin n) :
    (diagonalLaw n).map (fun z => z i) = gaussianReal 0 1 :=
  (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i).map_eq

theorem diagonalCoordinates_independent (n : ℕ) :
    iIndepFun (fun i : Fin n => fun z : Diagonals n => z i) (diagonalLaw n) :=
  iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)

theorem hasGaussianLaw_diagonalSum (n : ℕ) : HasGaussianLaw (diagonalSum n) (diagonalLaw n) :=
  (diagonalCoordinates_independent n).hasGaussianLaw_fun_sum
    (fun i => Paper.standardGaussianCoordinate_gaussian _ _ (measurable_pi_apply i)
      (diagonalCoordinate_law n i))

theorem integral_diagonalSum (n : ℕ) : (∫ z,diagonalSum n z ∂diagonalLaw n) = 0 := by
  have hg (i : Fin n) := Paper.standardGaussianCoordinate_gaussian _ _
    (measurable_pi_apply i) (diagonalCoordinate_law n i)
  unfold diagonalSum
  rw [integral_finsetSum _ (fun i _ => (hg i).integrable)]
  apply Finset.sum_eq_zero
  intro i _
  exact Paper.standardGaussianCoordinate_mean _ _ (measurable_pi_apply i)
    (diagonalCoordinate_law n i)

theorem variance_diagonalSum (n : ℕ) : variance (diagonalSum n) (diagonalLaw n) = n := by
  have hh := variance_sum_pi (μ := fun _ : Fin n => gaussianReal 0 1)
    (X := fun _ => id) (fun _ => memLp_id_gaussianReal' (p := 2) (by norm_num))
  have heq : (∑ i : Fin n, fun z : Diagonals n => id (z i)) = diagonalSum n := by
    funext z
    simp [diagonalSum]
  rw [heq] at hh
  change variance (diagonalSum n) (diagonalLaw n) = _ at hh
  rw [hh]
  simp only [variance_id_gaussianReal, NNReal.coe_one, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

theorem hasLaw_goeDiagonalNoise (n : ℕ) (hn : 0 < n) :
    HasLaw (goeDiagonalNoise n) (gaussianReal 0 (1/2)) (diagonalLaw n) := by
  have hg := (hasGaussianLaw_diagonalSum n).fun_smul (1/Real.sqrt (2*(n : ℝ)))
  change HasGaussianLaw (goeDiagonalNoise n) (diagonalLaw n) at hg
  have hmean : (∫ z,goeDiagonalNoise n z ∂diagonalLaw n) = 0 := by
    unfold goeDiagonalNoise
    rw [integral_const_mul,integral_diagonalSum,mul_zero]
  have hvar : variance (goeDiagonalNoise n) (diagonalLaw n) = (1/2 : ℝ) := by
    have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    unfold goeDiagonalNoise
    rw [variance_const_mul,variance_diagonalSum,div_pow,
      Real.sq_sqrt (by positivity : 0 ≤ 2*(n : ℝ))]
    field_simp
  refine ⟨hg.aemeasurable, ?_⟩
  rw [hg.map_eq_gaussianReal,hmean,hvar]
  congr 1
  apply NNReal.coe_injective
  simp

def completionMap (n : ℕ) (p : GOEDisorder n) : Couplings n × ℝ :=
  (p.1,goeDiagonalNoise n p.2)

theorem measurable_completionMap (n : ℕ) : Measurable (completionMap n) := by
  unfold completionMap goeDiagonalNoise diagonalSum
  fun_prop

theorem goeLaw_map_completionMap (n : ℕ) (hn : 0 < n) :
    (goeLaw n).map (completionMap n) = completionLaw n := by
  unfold goeLaw completionLaw completionMap
  have hm := Measure.map_prod_map (couplingLaw n) (diagonalLaw n)
    (f := id) (g := goeDiagonalNoise n) measurable_id
      (show Measurable (goeDiagonalNoise n) by
        unfold goeDiagonalNoise diagonalSum
        fun_prop)
  calc
    _ = (Measure.map id (couplingLaw n)).prod (Measure.map (goeDiagonalNoise n) (diagonalLaw n)) := hm.symm
    _ = _ := by rw [Measure.map_id,(hasLaw_goeDiagonalNoise n hn).map_eq]

theorem goeMatrix_diagonal (n : ℕ) (p : GOEDisorder n) (i : Fin n) :
    goeMatrix n p i i = Real.sqrt (2/(n : ℝ))*p.2 i := by
  unfold goeMatrix
  have hz (e : Edge n) :
      (if i = e.val.1 then (1:ℝ) else 0)*(if i = e.val.2 then 1 else 0)+
      (if i = e.val.2 then (1:ℝ) else 0)*(if i = e.val.1 then 1 else 0) = 0 := by
    have he := ne_of_lt e.property
    split_ifs <;> simp_all
  simp only [hz,mul_zero,Finset.sum_const_zero,ite_true,zero_add]

theorem goeMatrix_half_trace (n : ℕ) (hn : 0 < n) (p : GOEDisorder n) :
    (1/2 : ℝ)*Matrix.trace (goeMatrix n p) = goeDiagonalNoise n p.2 := by
  have hs : (1/2 : ℝ)*Real.sqrt (2/(n : ℝ)) = 1/Real.sqrt (2*(n : ℝ)) := by
    have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
    have ha : 0 ≤ (1/2 : ℝ)*Real.sqrt (2/(n : ℝ)) := by positivity
    have hb : 0 ≤ 1/Real.sqrt (2*(n : ℝ)) := by positivity
    apply (sq_eq_sq₀ ha hb).mp
    simp only [mul_pow,div_pow]
    rw [Real.sq_sqrt (by positivity),Real.sq_sqrt (by positivity)]
    field_simp
  unfold Matrix.trace Matrix.diag goeDiagonalNoise diagonalSum
  simp_rw [goeMatrix_diagonal]
  rw [← Finset.mul_sum,← mul_assoc,hs]

end QuantitativePaper
