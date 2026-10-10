module
public import Mathlib.Analysis.Normed.Affine.Convex
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv

@[expose] public section

/-! Quantitative derivative interpolation for Banach-valued functions.
This permits passing higher actual jets through uniform approximation, rather
than assigning formal derivatives to the chosen limit. -/
noncomputable section
open Set Filter
open scoped NNReal
namespace FourPapersCommon
set_option maxHeartbeats 800000
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem firstTaylor_remainder_Banach (f : E→F) (hf : Differentiable ℝ f)
    (L : ℝ≥0) (hL : LipschitzWith L (fderiv ℝ f)) (x v : E) :
    ‖f (x+v)-f x-fderiv ℝ f x v‖ ≤ L*‖v‖^2 := by
  have hb (y : E) (hy : y∈segment ℝ x (x+v)) :
      ‖fderiv ℝ f y-fderiv ℝ f x‖ ≤ L*‖v‖ := by
    have hh := dist_add_dist_of_mem_segment hy
    have hd : dist y x ≤ ‖v‖ := by
      rw [dist_comm y x]
      have he : dist x (x+v)=‖v‖ := by rw [dist_eq_norm];simp
      rw [he] at hh
      linarith [dist_nonneg (x := y) (y := x+v)]
    rw [dist_eq_norm] at hd
    exact (hL.norm_sub_le y x).trans (mul_le_mul_of_nonneg_left hd L.coe_nonneg)
  have hh := (convex_segment x (x+v)).norm_image_sub_le_of_norm_fderiv_le'
    (fun y _ => hf y) hb (left_mem_segment ℝ x (x+v)) (right_mem_segment ℝ x (x+v))
  simpa only [add_sub_cancel_left,pow_two,mul_assoc] using hh

theorem norm_fderiv_sub_le_of_uniform_sub_Banach (f g : E→F)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (L : ℝ≥0)
    (hLf : LipschitzWith L (fderiv ℝ f)) (hLg : LipschitzWith L (fderiv ℝ g))
    (ε : ℝ) (hε : 0≤ε) (hb : ∀y,‖f y-g y‖≤ε)
    (δ : ℝ) (hδ : 0<δ) (x : E) :
    ‖fderiv ℝ f x-fderiv ℝ g x‖ ≤ 2*ε/δ+2*L*δ := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro w hw
  have hfw := firstTaylor_remainder_Banach f hf L hLf x (δ•w)
  have hgw := firstTaylor_remainder_Banach g hg L hLg x (δ•w)
  have hv : ‖δ•w‖=δ := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos hδ,hw,mul_one]
  rw [hv] at hfw hgw
  have hval : ‖(f (x+δ•w)-f x)-(g (x+δ•w)-g x)‖≤2*ε := by
    calc
      _ = ‖(f (x+δ•w)-g (x+δ•w))-(f x-g x)‖ := by congr 1;abel
      _ ≤ ‖f (x+δ•w)-g (x+δ•w)‖+‖f x-g x‖ := norm_sub_le _ _
      _ ≤ 2*ε := by linarith [hb (x+δ•w),hb x]
  have hder : ‖fderiv ℝ f x (δ•w)-fderiv ℝ g x (δ•w)‖≤2*ε+2*L*δ^2 := by
    calc
      _ = ‖((f (x+δ•w)-f x)-(g (x+δ•w)-g x))-
          (f (x+δ•w)-f x-fderiv ℝ f x (δ•w))+
          (g (x+δ•w)-g x-fderiv ℝ g x (δ•w))‖ := by congr 1;abel
      _ ≤ ‖(f (x+δ•w)-f x)-(g (x+δ•w)-g x)‖+
          ‖f (x+δ•w)-f x-fderiv ℝ f x (δ•w)‖+
          ‖g (x+δ•w)-g x-fderiv ℝ g x (δ•w)‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ _ := by linarith
  have hh : δ*‖(fderiv ℝ f x-fderiv ℝ g x) w‖≤2*ε+2*L*δ^2 := by
    simpa only [map_smul,ContinuousLinearMap.sub_apply,←smul_sub,norm_smul,
      Real.norm_eq_abs,abs_of_pos hδ] using hder
  have he : 2*ε/δ+2*L*δ=(2*ε+2*L*δ^2)/δ := by field_simp
  rw [he]
  exact (le_div_iff₀ hδ).mpr (by simpa only [mul_comm] using hh)

theorem norm_fderiv_sub_le_sqrt_Banach (f g : E→F)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (L : ℝ≥0)
    (hLf : LipschitzWith L (fderiv ℝ f)) (hLg : LipschitzWith L (fderiv ℝ g))
    (a d : ℝ) (ha : 0≤a) (hd : 0≤d) (hb : ∀y,‖f y-g y‖≤a*d) (x : E) :
    ‖fderiv ℝ f x-fderiv ℝ g x‖≤2*(a+L)*Real.sqrt d := by
  by_cases h0 : d=0
  · have he : f=g := by
      funext y
      have hh := hb y
      rw [h0,mul_zero,norm_le_zero_iff,sub_eq_zero] at hh
      exact hh
    rw [he,sub_self,norm_zero]
    positivity
  · have hdp : 0<d := lt_of_le_of_ne hd (Ne.symm h0)
    have hs := Real.sqrt_pos.mpr hdp
    have hh := norm_fderiv_sub_le_of_uniform_sub_Banach f g hf hg L hLf hLg (a*d)
      (mul_nonneg ha hd) hb (Real.sqrt d) hs x
    refine hh.trans_eq ?_
    rw [←Real.sq_sqrt hd,Real.sqrt_sq hs.le]
    field_simp

end FourPapersCommon
