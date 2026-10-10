module
public import FourPapersCommon.OneSidedRemainder
public import FourPapersCommon.IntegrableTruncation
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul

@[expose] public section

/-! An actual exponential-moment derivative from a weighted increment
derivative and a uniform first-order increment bound. All quadratic exponential
remainders are integrated against the genuine initial exponential weight. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace FourPapersCommon
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem norm_exp_sub_one_sub_id_le_global (x : ℝ) :
    ‖Real.exp x-1-x‖ ≤ ‖x‖^2*Real.exp ‖x‖ := by
  have hh := Complex.norm_exp_sub_sum_le_norm_mul_exp (x : ℂ) 2
  have he : Complex.exp (x : ℂ)-(1+(x : ℂ)) = ((Real.exp x-(1+x) : ℝ) : ℂ) := by
    rw [←Complex.ofReal_exp]
    push_cast
    rfl
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,pow_zero,pow_one,Nat.factorial_zero,Nat.factorial_one,Nat.cast_one,div_one,zero_add] at hh
  rw [he] at hh
  simpa only [Complex.norm_real,Real.norm_eq_abs,sq_abs,sub_sub] using hh

theorem hasDerivWithinAt_integral_exp_of_weighted_increment
    (U : ℝ → Ω → ℝ) (a R d : ℝ) (hR : 0 ≤ R)
    (hUm : ∀lam,Measurable (U lam))
    (hUi : ∀lam ∈ Icc (0 : ℝ) 1,Integrable (fun ω => Real.exp (a*U lam ω)) P)
    (hinc : ∀lam ∈ Icc (0 : ℝ) 1,∀ω,‖U lam ω-U 0 ω‖ ≤ R*‖lam‖)
    (hd : HasDerivWithinAt (fun lam => ∫ω,Real.exp (a*U 0 ω)*(U lam ω-U 0 ω) ∂P)
      d (Icc (0 : ℝ) 1) 0) :
    HasDerivWithinAt (fun lam => ∫ω,Real.exp (a*U lam ω) ∂P)
      (a*d) (Icc (0 : ℝ) 1) 0 := by
  let W := fun ω => Real.exp (a*U 0 ω)
  let J := fun lam => ∫ω,W ω*(U lam ω-U 0 ω) ∂P
  let M := fun lam => ∫ω,Real.exp (a*U lam ω) ∂P
  let C := a^2*R^2*Real.exp (|a| *R)*(∫ω,W ω ∂P)
  have hiW : Integrable W P := hUi 0 ⟨le_rfl,zero_le_one⟩
  have hWn (ω) : 0 ≤ W ω := (Real.exp_pos _).le
  have hiJ (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) 1) :
      Integrable (fun ω => W ω*(U lam ω-U 0 ω)) P :=
    integrable_weight_mul_bounded W _ hiW ((hUm lam).sub (hUm 0)) (R*‖lam‖) (hinc lam hlam)
  have hCn : 0 ≤ C := by
    have hMn : 0 ≤ ∫ω,W ω ∂P := integral_nonneg hWn
    dsimp only [C]
    positivity
  have hbound (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) 1) :
      ‖M lam-M 0-a*J lam‖ ≤ C*lam^2 := by
    have hip := (hUi lam hlam).sub hiW
    have hij := (hiJ lam hlam).const_mul a
    have he : M lam-M 0-a*J lam =
        ∫ω,Real.exp (a*U lam ω)-W ω-a*(W ω*(U lam ω-U 0 ω)) ∂P := by
      dsimp only [M,J]
      have h0 := integral_sub (hUi lam hlam) hiW
      have h1 := integral_sub hip hij
      simp only [Pi.sub_apply] at h0 h1
      rw [integral_const_mul,h0] at h1
      exact h1.symm
    rw [he]
    have hh := norm_integral_le_of_norm_le
      (f := fun ω => Real.exp (a*U lam ω)-W ω-a*(W ω*(U lam ω-U 0 ω)))
      (g := fun ω => (a^2*R^2*Real.exp (|a| *R)*lam^2)*W ω)
      (hiW.const_mul _)
      (Eventually.of_forall (fun ω => by
        let δ := U lam ω-U 0 ω
        have hδ : ‖δ‖ ≤ R*lam := by simpa only [δ,Real.norm_of_nonneg hlam.1] using hinc lam hlam ω
        have hx : ‖a*δ‖ ≤ |a| *R := by
          rw [norm_mul,Real.norm_eq_abs]
          exact (mul_le_mul_of_nonneg_left hδ (abs_nonneg _)).trans
            (by
              have hh := mul_le_mul_of_nonneg_left hlam.2 (mul_nonneg (abs_nonneg a) hR)
              simpa only [mul_assoc,mul_one] using hh)
        have hx2 : ‖a*δ‖^2 ≤ a^2*R^2*lam^2 := by
          have ha := mul_le_mul_of_nonneg_left hδ (abs_nonneg a)
          rw [←Real.norm_eq_abs,←norm_mul] at ha
          have hh := pow_le_pow_left₀ (norm_nonneg _) ha 2
          simpa only [mul_pow,Real.norm_eq_abs,sq_abs,mul_assoc] using hh
        have heq : Real.exp (a*U lam ω)-W ω-a*(W ω*(U lam ω-U 0 ω)) =
            W ω*(Real.exp (a*δ)-1-a*δ) := by
          dsimp only [W,δ]
          rw [show a*U lam ω = a*U 0 ω+a*(U lam ω-U 0 ω) from by ring,Real.exp_add]
          ring
        rw [heq,norm_mul,Real.norm_of_nonneg (hWn ω)]
        have hc := (norm_exp_sub_one_sub_id_le_global (a*δ)).trans
          (mul_le_mul hx2 (Real.exp_le_exp.mpr hx) (Real.exp_pos _).le (by positivity))
        exact (mul_le_mul_of_nonneg_left hc (hWn ω)).trans_eq (by ring)))
    rw [integral_const_mul] at hh
    convert hh using 1
    dsimp only [C]
    ring
  let E := fun lam => M lam-M 0-a*J lam
  have hE : HasDerivWithinAt E 0 (Icc (0 : ℝ) 1) 0 := by
    apply hasDerivWithinAt_Icc_zero_of_error_bound (error := fun lam => C*lam)
    · simpa only [mul_zero] using
        (show Tendsto (fun lam : ℝ => lam) (𝓝[Icc (0 : ℝ) 1] 0) (𝓝 0) from nhdsWithin_le_nhds).const_mul C
    · intro lam hlam
      exact mul_nonneg hCn hlam.1
    · intro lam hlam
      have he0 : E 0=0 := by simp [E,J]
      rw [he0,mul_zero,sub_zero,sub_zero]
      exact (hbound lam hlam).trans_eq (by ring)
  have hd' : HasDerivWithinAt J d (Icc (0 : ℝ) 1) 0 := hd
  have hh := (hE.add (hd'.const_mul a)).add_const (M 0)
  convert hh using 1
  · ext lam
    dsimp only [E,M,J,Pi.add_apply]
    ring
  · ring

end FourPapersCommon
