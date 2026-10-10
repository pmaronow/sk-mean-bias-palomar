module
public import QuantitativeFollowup.GaussianShiftExponentialSmooth
public import QuantitativeFollowup.ScalarFiniteHeatData
public import FourPapersCommon.ExponentialLinearChange

@[expose] public section

/-! Actual linear, nonlinear composition and exponential closure on an
unbounded open domain with explicit growth envelopes. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper
set_option maxHeartbeats 2200000
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exponentialSmoothOn_linear (A : E →L[ℝ] F) (U : Set E) :
    ExponentialSmoothOn (A : E → F) U := by
  refine ⟨fun _ _ => A.contDiff.contDiffAt, fun r => ⟨‖A‖, 1, norm_nonneg _, by norm_num, ?_⟩⟩
  intro x hx
  rw [one_mul]
  cases r with
  | zero =>
    rw [norm_iteratedFDeriv_zero]
    apply (A.le_opNorm x).trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    linarith [Real.add_one_le_exp ‖x‖]
  | succ r =>
    rw [←norm_iteratedFDeriv_fderiv]
    have he : fderiv ℝ (A : E → F) = fun _ => A := funext fun x => A.fderiv
    rw [he]
    cases r with
    | zero =>
      rw [norm_iteratedFDeriv_zero]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (Real.one_le_exp_iff.mpr (norm_nonneg x)) (norm_nonneg A)
    | succ r =>
      rw [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero]
      positivity

theorem exponentialSmoothOn_comp_boundedPositiveJets
    (f : ℝ → ℝ) (hf : BoundedPositiveJets f)
    (B L : ℝ) (hB : 0 ≤ B) (hL : 0 ≤ L) (hv : ∀ y, |f y| ≤ B+L*|y|)
    (g : E → ℝ) (U : Set E) (hg : ExponentialSmoothOn g U)
    (S T : ℝ) (hS : 0 ≤ S) (hT : 0 ≤ T) (hgv : ∀ x ∈ U, |g x| ≤ S+T*‖x‖) :
    ExponentialSmoothOn (f ∘ g) U := by
  classical
  refine ⟨fun x hx => hf.1.contDiffAt.comp x (hg.smooth x hx), fun r => ?_⟩
  choose K hK hb using fun i : Fin r => hf.2 (i+1) (by omega)
  let J := B+L*S+L*T+∑ i, K i
  have hsumK := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hK i)
  have hJ : 0 ≤ J := by
    dsimp only [J]
    exact add_nonneg (add_nonneg (add_nonneg hB (mul_nonneg hL hS)) (mul_nonneg hL hT)) hsumK
  have houter (x : E) (hx : x ∈ U) (i : ℕ) (hi : i ≤ r) :
      ‖iteratedFDeriv ℝ i f (g x)‖ ≤ J*Real.exp ‖x‖ := by
    cases i with
    | zero =>
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
      have hlin : |f (g x)| ≤ B+L*S+L*T*‖x‖ := by
        have hh := mul_le_mul_of_nonneg_left (hgv x hx) hL
        nlinarith only [hv (g x), hh]
      have hpow : ‖x‖ ≤ Real.exp ‖x‖ := by linarith [Real.add_one_le_exp ‖x‖]
      have he : 1 ≤ Real.exp ‖x‖ := Real.one_le_exp_iff.mpr (norm_nonneg x)
      have hsum := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hK i)
      have h0 := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ B+L*S)
      have h1 := mul_le_mul_of_nonneg_left hpow (mul_nonneg hL hT)
      have h2 := mul_nonneg hsum (Real.exp_pos ‖x‖).le
      dsimp only [J]
      nlinarith only [hlin,h0,h1,h2]
    | succ i =>
      let j : Fin r := ⟨i, by omega⟩
      have hk : K j ≤ J := by
        have hh := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => hK i) (Finset.mem_univ j)
        dsimp only [J]
        linarith [mul_nonneg hL hS, mul_nonneg hL hT]
      exact (hb j (g x)).trans (hk.trans (by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (Real.one_le_exp_iff.mpr (norm_nonneg x)) hJ))
  obtain ⟨C,D,hC,hD,hgj⟩ := hg.common_bound r
  refine ⟨(r.factorial:ℝ)*J*C^r, 1+(r:ℝ)*D, by positivity, by positivity, ?_⟩
  intro x hx
  have hbase : 1 ≤ C*Real.exp (D*‖x‖) := one_le_mul_of_one_le_of_one_le hC
    (Real.one_le_exp_iff.mpr (mul_nonneg hD (norm_nonneg x)))
  apply (DepthPaper.norm_iteratedFDeriv_comp_le_at hf.1.contDiffAt (hg.smooth x hx)
    r (J*Real.exp ‖x‖) (C*Real.exp (D*‖x‖)) (houter x hx)
    (fun i hi hir => (hgj i hir x hx).trans (le_self_pow₀ hbase (by omega)))).trans_eq
  rw [mul_pow, ←Real.exp_nat_mul]
  rw [show (1+(r:ℝ)*D)*‖x‖ = ‖x‖+(r:ℝ)*(D*‖x‖) by ring, Real.exp_add]
  ring

theorem exponentialSmoothOn_exp_of_linear_bound (f : E → ℝ) (U : Set E)
    (hf : ExponentialSmoothOn f U) (B L : ℝ) (hL : 0 ≤ L)
    (hv : ∀ x ∈ U, f x ≤ B+L*‖x‖) :
    ExponentialSmoothOn (fun x => Real.exp (f x)) U := by
  refine ⟨fun x hx => (hf.smooth x hx).exp, fun r => ?_⟩
  obtain ⟨C,D,hC,hD,hj⟩ := hf.common_bound r
  refine ⟨(r.factorial:ℝ)*Real.exp B*C^r, L+(r:ℝ)*D, by positivity, by positivity, ?_⟩
  intro x hx
  have hbase : 1 ≤ C*Real.exp (D*‖x‖) := one_le_mul_of_one_le_of_one_le hC
    (Real.one_le_exp_iff.mpr (mul_nonneg hD (norm_nonneg x)))
  have houter (i : ℕ) (_ : i ≤ r) :
      ‖iteratedFDeriv ℝ i Real.exp (f x)‖ ≤ Real.exp (B+L*‖x‖) := by
    have he : iteratedDeriv i Real.exp = Real.exp := by
      simpa only [one_mul, one_pow] using iteratedDeriv_exp_const_mul i 1
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, he, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (hv x hx)
  have hh := DepthPaper.norm_iteratedFDeriv_comp_le_at Real.contDiff_exp.contDiffAt
    (hf.smooth x hx) r (Real.exp (B+L*‖x‖)) (C*Real.exp (D*‖x‖)) houter
    (fun i hi hir => (hj i hir x hx).trans (le_self_pow₀ hbase (by omega)))
  apply hh.trans_eq
  rw [mul_pow, ←Real.exp_nat_mul, Real.exp_add]
  rw [show (L+(r:ℝ)*D)*‖x‖ = L*‖x‖+(r:ℝ)*(D*‖x‖) by ring, Real.exp_add]
  ring

end QuantitativeFollowup
