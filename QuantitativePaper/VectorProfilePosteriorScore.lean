module
public import QuantitativePaper.VectorProfileUniformNodeVariation
public import QuantitativePaper.VectorProfileEndpointSmooth
public import QuantitativePaper.VectorTailScoreBounds
public import Mathlib.Analysis.Calculus.Deriv.Add

@[expose] public section

/-! The actual remaining posterior has a fixed Gaussian reference as affine
profile masses vary. Its literal first score is differentiated here; the
Stieltjes direction has total variation at most two, independently of depth.
These are genuine density and derivative identities, not conditional-law
inputs. -/
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology NNReal ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

def vectorProfilePosteriorWeight (s₀ s₁ : RSBScheme k) (N : ℕ)
    (θ : ℝ) (i : Option (Fin N)) : ℝ :=
  (1-θ)*vectorTailStieltjesWeight s₀ N i+θ*vectorTailStieltjesWeight s₁ N i

def vectorProfilePosteriorDirection (s₀ s₁ : RSBScheme k) (N : ℕ)
    (i : Option (Fin N)) : ℝ :=
  vectorTailStieltjesWeight s₁ N i-vectorTailStieltjesWeight s₀ N i

def vectorProfilePosteriorPotential (s₀ s₁ : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (x : Field n) (N : ℕ) (z : Fin (N+1)→Field n)
    (θ : ℝ) : Option (Fin N)→ℝ
  | none => vectorProfileRecursion s₀ s₁ β t θ p (N+1) x
  | some i => vectorProfileRecursion s₀ s₁ β t θ p (N+1-(i+1))
      (historyExtended (vectorHistoryFrom s₀ β t (k+2-(N+1)) p x (N+1) z) (i+1)).2

def vectorProfilePosteriorLogDensity (s₀ s₁ : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (x : Field n) (N : ℕ) (θ : ℝ)
    (z : (Fin (N+1)→Field n)×Configuration n) : ℝ :=
  vectorTerminalExponent n β t p
      (vectorHistoryFrom s₀ β t (k+2-(N+1)) p x (N+1) z.1 (Fin.last (N+1))).2 z.2-
    ∑i : Option (Fin N),vectorProfilePosteriorWeight s₀ s₁ N θ i*
      vectorProfilePosteriorPotential s₀ s₁ β t p x N z.1 θ i

theorem vectorHistoryFrom_profileScheme (s₀ s₁ : RSBScheme k) (β t θ : ℝ)
    (hθ : θ ∈ Icc (0:ℝ) 1) (L : ℕ) (p : Couplings n×ℝ)
    (x : Field n) (j : ℕ) (z : Fin j→Field n) :
    vectorHistoryFrom (vectorProfileScheme s₀ s₁ θ hθ) β t L p x j z=
      vectorHistoryFrom s₀ β t L p x j z := by rfl

theorem vectorProfilePosteriorWeight_eq_scheme (s₀ s₁ : RSBScheme k)
    (N : ℕ) (θ : ℝ) (hθ : θ ∈ Icc (0:ℝ) 1) (i : Option (Fin N)) :
    vectorProfilePosteriorWeight s₀ s₁ N θ i=
      vectorTailStieltjesWeight (vectorProfileScheme s₀ s₁ θ hθ) N i := by
  cases i <;> simp only [vectorProfilePosteriorWeight,vectorTailStieltjesWeight,
    vectorProfileScheme,vectorProfileMass] <;> ring

theorem vectorProfilePosteriorPotential_eq_scheme (s₀ s₁ : RSBScheme k) (β t θ : ℝ)
    (hθ : θ ∈ Icc (0:ℝ) 1) (p : Couplings n×ℝ) (x : Field n)
    (N : ℕ) (z : Fin (N+1)→Field n) (i : Option (Fin N)) :
    vectorProfilePosteriorPotential s₀ s₁ β t p x N z θ i=
      vectorTailStieltjesPotential (vectorProfileScheme s₀ s₁ θ hθ) β t p N z i x := by
  cases i with
  | none =>
    simp only [vectorProfilePosteriorPotential,vectorTailStieltjesPotential,
      vectorTailHistoryPotential_initial]
    exact congrFun (vectorProfileRecursion_eq_scheme s₀ s₁ β t θ hθ p (N+1)) x
  | some i =>
    simp only [vectorProfilePosteriorPotential,vectorTailStieltjesPotential,
      vectorTailHistoryPotential,vectorHistoryFrom_profileScheme]
    exact congrFun (vectorProfileRecursion_eq_scheme s₀ s₁ β t θ hθ p _) _

theorem vectorProfilePosteriorLogDensity_eq_scheme (s₀ s₁ : RSBScheme k)
    (β t θ : ℝ) (hθ : θ ∈ Icc (0:ℝ) 1) (p : Couplings n×ℝ)
    (x : Field n) (N : ℕ) (hN : N+1 ≤ k+2)
    (z : (Fin (N+1)→Field n)×Configuration n) :
    vectorProfilePosteriorLogDensity s₀ s₁ β t p x N θ z=
      vectorTailPosteriorLogDensity (vectorProfileScheme s₀ s₁ θ hθ) β t p x (N+1) z := by
  rw [vectorTailPosteriorLogDensity_stieltjes _ β t p x N hN]
  rw [vectorHistoryFrom_profileScheme]
  unfold vectorProfilePosteriorLogDensity
  rw [Fintype.sum_option]
  simp_rw [vectorProfilePosteriorWeight_eq_scheme s₀ s₁ N θ hθ,
    vectorProfilePosteriorPotential_eq_scheme s₀ s₁ β t θ hθ p x N z.1]
  simp only [vectorTailStieltjesWeight,vectorTailStieltjesPotential]
  rw [Fin.sum_univ_eq_sum_range (fun i =>
    ((vectorProfileScheme s₀ s₁ θ hθ).m (k+2-(N+1)+(i+1))-
      (vectorProfileScheme s₀ s₁ θ hθ).m (k+2-(N+1)+i))*
      vectorTailHistoryPotential (vectorProfileScheme s₀ s₁ θ hθ) β t p x (N+1) (i+1) z.1) N]
  ring

theorem integral_exp_vectorProfilePosteriorLogDensity (s₀ s₁ : RSBScheme k)
    (β t θ : ℝ) (hθ : θ ∈ Icc (0:ℝ) 1) (p : Couplings n×ℝ)
    (x : Field n) (N : ℕ) (hN : N+1 ≤ k+2) :
    (∫z,Real.exp (vectorProfilePosteriorLogDensity s₀ s₁ β t p x N θ z)
      ∂vectorTailGaussianBase n (N+1))=1 := by
  simp_rw [vectorProfilePosteriorLogDensity_eq_scheme s₀ s₁ β t θ hθ p x N hN]
  exact integral_vectorTailPosterior_exp _ β t p x (N+1) hN

theorem vectorProfilePosteriorWeight_nonneg (s₀ s₁ : RSBScheme k)
    (N : ℕ) (hN : N+1 ≤ k+2) (θ : ℝ) (hθ : θ ∈ Icc (0:ℝ) 1)
    (i : Option (Fin N)) : 0 ≤ vectorProfilePosteriorWeight s₀ s₁ N θ i := by
  exact add_nonneg (mul_nonneg (sub_nonneg.mpr hθ.2)
    (vectorTailStieltjesWeight_nonneg s₀ N hN i))
    (mul_nonneg hθ.1 (vectorTailStieltjesWeight_nonneg s₁ N hN i))

theorem vectorProfilePosteriorWeight_sum (s₀ s₁ : RSBScheme k)
    (N : ℕ) (hN : N+1 ≤ k+2) (θ : ℝ) :
    (∑i : Option (Fin N),vectorProfilePosteriorWeight s₀ s₁ N θ i)=1 := by
  simp only [vectorProfilePosteriorWeight,Finset.sum_add_distrib,←Finset.mul_sum,
    vectorTailStieltjesWeight_sum s₀ N hN,vectorTailStieltjesWeight_sum s₁ N hN,mul_one]
  ring

theorem vectorProfilePosteriorDirection_sum_zero (s₀ s₁ : RSBScheme k)
    (N : ℕ) (hN : N+1 ≤ k+2) :
    (∑i : Option (Fin N),vectorProfilePosteriorDirection s₀ s₁ N i)=0 := by
  simp only [vectorProfilePosteriorDirection,Finset.sum_sub_distrib,
    vectorTailStieltjesWeight_sum s₀ N hN,vectorTailStieltjesWeight_sum s₁ N hN,sub_self]

theorem vectorProfilePosteriorDirection_total_variation_le (s₀ s₁ : RSBScheme k)
    (N : ℕ) (hN : N+1 ≤ k+2) :
    (∑i : Option (Fin N),|vectorProfilePosteriorDirection s₀ s₁ N i|) ≤ 2 := by
  calc
    _ ≤ ∑i : Option (Fin N),(vectorTailStieltjesWeight s₁ N i+
        vectorTailStieltjesWeight s₀ N i) := Finset.sum_le_sum fun i _ => by
      unfold vectorProfilePosteriorDirection
      exact (abs_sub _ _).trans_eq (by
        rw [abs_of_nonneg (vectorTailStieltjesWeight_nonneg s₁ N hN i),
          abs_of_nonneg (vectorTailStieltjesWeight_nonneg s₀ N hN i)])
    _ = 2 := by rw [Finset.sum_add_distrib,vectorTailStieltjesWeight_sum s₀ N hN,
        vectorTailStieltjesWeight_sum s₁ N hN];norm_num

theorem contDiff_vectorProfilePosteriorPotential_theta (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (p : Couplings n×ℝ) (x : Field n) (N : ℕ)
    (z : Fin (N+1)→Field n) (i : Option (Fin N)) :
    ContDiff ℝ ∞ (fun θ => vectorProfilePosteriorPotential s₀ s₁ β t p x N z θ i) := by
  cases i with
  | none =>
    change ContDiff ℝ ∞ (fun θ => vectorProfileRecursion s₀ s₁ β t θ p (N+1) x)
    exact (contDiff_vectorProfileJointFunction_all_theta (n:=n) s₀ s₁ β t (N+1)).comp
      (contDiff_id.prodMk (contDiff_const (c:=(p,x))))
  | some i =>
    change ContDiff ℝ ∞ (fun θ => vectorProfileRecursion s₀ s₁ β t θ p _ _)
    exact (contDiff_vectorProfileJointFunction_all_theta (n:=n) s₀ s₁ β t (N+1-(i+1))).comp
      (contDiff_id.prodMk (contDiff_const (c:=(p,
        (historyExtended (vectorHistoryFrom s₀ β t (k+2-(N+1)) p x (N+1) z) (i+1)).2))))

theorem hasDerivAt_vectorProfilePosteriorWeight (s₀ s₁ : RSBScheme k)
    (N : ℕ) (i : Option (Fin N)) (θ : ℝ) :
    HasDerivAt (fun φ => vectorProfilePosteriorWeight s₀ s₁ N φ i)
      (vectorProfilePosteriorDirection s₀ s₁ N i) θ := by
  have hh := (((hasDerivAt_const θ (1:ℝ)).sub (hasDerivAt_id θ)).mul_const
    (vectorTailStieltjesWeight s₀ N i)).add
      ((hasDerivAt_id θ).mul_const (vectorTailStieltjesWeight s₁ N i))
  convert hh using 1
  · rfl
  · simp only [vectorProfilePosteriorDirection,zero_sub,one_mul,neg_one_mul]
    ring

theorem hasDerivAt_vectorProfilePosteriorLogDensity (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (p : Couplings n×ℝ) (x : Field n) (N : ℕ) (θ : ℝ)
    (z : (Fin (N+1)→Field n)×Configuration n) :
    HasDerivAt (fun φ => vectorProfilePosteriorLogDensity s₀ s₁ β t p x N φ z)
      (-(∑i : Option (Fin N), (vectorProfilePosteriorDirection s₀ s₁ N i*
          vectorProfilePosteriorPotential s₀ s₁ β t p x N z.1 θ i+
        vectorProfilePosteriorWeight s₀ s₁ N θ i*
          deriv (fun φ : ℝ => vectorProfilePosteriorPotential s₀ s₁ β t p x N z.1 φ (i : Option (Fin N))) θ))) θ := by
  have hd := HasDerivAt.sum (u:=Finset.univ) (fun (i : Option (Fin N)) _ =>
    (hasDerivAt_vectorProfilePosteriorWeight s₀ s₁ N i θ).mul
      (((contDiff_vectorProfilePosteriorPotential_theta s₀ s₁ β t p x N z.1 i).differentiable
        (by simp) θ).hasDerivAt))
  have hh := (hasDerivAt_const θ (vectorTerminalExponent n β t p
      (vectorHistoryFrom s₀ β t (k+2-(N+1)) p x (N+1) z.1 (Fin.last (N+1))).2 z.2)).sub hd
  convert hh using 1
  · funext φ
    simp only [vectorProfilePosteriorLogDensity,Pi.sub_apply,Pi.mul_apply,Finset.sum_apply]
  · simp only [zero_sub]

end QuantitativePaper
