module
public import QuantitativePaper.VectorFiniteTailGradient
public import Mathlib.Analysis.Normed.Affine.Convex

@[expose] public section

/-! Genuine derivative stability from a uniform value estimate and a
uniform Lipschitz derivative. This supplies gradient convergence without
assuming a differential equation for a chosen uniform limit. -/
noncomputable section
open Set
open scoped NNReal
namespace QuantitativePaper
set_option maxHeartbeats 400000

theorem firstTaylor_remainder_of_lipschitz_fderiv {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E→ℝ)
    (hf : Differentiable ℝ f) (L : ℝ≥0)
    (hL : LipschitzWith L (fderiv ℝ f)) (x v : E) :
    ‖f (x+v)-f x-fderiv ℝ f x v‖ ≤ L*‖v‖^2 := by
  have hb (y : E) (hy : y∈segment ℝ x (x+v)) :
      ‖fderiv ℝ f y-fderiv ℝ f x‖ ≤ L*‖v‖ := by
    have hh := dist_add_dist_of_mem_segment hy
    have hd : dist y x ≤ ‖v‖ := by
      rw [dist_comm y x]
      have he : dist x (x+v)=‖v‖ := by rw [dist_eq_norm];simp
      rw [he] at hh
      linarith [show 0≤dist y (x+v) from dist_nonneg]
    rw [dist_eq_norm] at hd
    exact (hL.norm_sub_le y x).trans (mul_le_mul_of_nonneg_left hd L.coe_nonneg)
  have hh := (convex_segment x (x+v)).norm_image_sub_le_of_norm_fderiv_le'
    (fun y _ => hf y) hb (left_mem_segment ℝ x (x+v)) (right_mem_segment ℝ x (x+v))
  simpa only [add_sub_cancel_left,pow_two,mul_assoc] using hh

theorem norm_fderiv_sub_le_of_uniform_sub {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f g : E→ℝ)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (L : ℝ≥0)
    (hLf : LipschitzWith L (fderiv ℝ f)) (hLg : LipschitzWith L (fderiv ℝ g))
    (ε : ℝ) (hε : 0≤ε) (hb : ∀y,|f y-g y|≤ε)
    (δ : ℝ) (hδ : 0<δ) (x : E) :
    ‖fderiv ℝ f x-fderiv ℝ g x‖ ≤ 2*ε/δ+2*L*δ := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro w hw
  have hfw := firstTaylor_remainder_of_lipschitz_fderiv f hf L hLf x (δ•w)
  have hgw := firstTaylor_remainder_of_lipschitz_fderiv g hg L hLg x (δ•w)
  have hv : ‖δ•w‖=δ := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos hδ,hw,mul_one]
  rw [hv] at hfw hgw
  have hval : |(f (x+δ•w)-f x)-(g (x+δ•w)-g x)|≤2*ε := by
    calc
      _ = |(f (x+δ•w)-g (x+δ•w))-(f x-g x)| := by congr 1;ring
      _ ≤ |f (x+δ•w)-g (x+δ•w)|+|f x-g x| := abs_sub _ _
      _ ≤ 2*ε := by linarith [hb (x+δ•w),hb x]
  have hder : |fderiv ℝ f x (δ•w)-fderiv ℝ g x (δ•w)|≤2*ε+2*L*δ^2 := by
    calc
      _ = |((f (x+δ•w)-f x)-(g (x+δ•w)-g x))-
          (f (x+δ•w)-f x-fderiv ℝ f x (δ•w))+
          (g (x+δ•w)-g x-fderiv ℝ g x (δ•w))| := by congr 1;ring
      _ ≤ |(f (x+δ•w)-f x)-(g (x+δ•w)-g x)|+
          |f (x+δ•w)-f x-fderiv ℝ f x (δ•w)|+
          |g (x+δ•w)-g x-fderiv ℝ g x (δ•w)| := by
        exact (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ _ := by
        rw [Real.norm_eq_abs] at hfw hgw
        linarith
  have hh : δ*‖(fderiv ℝ f x-fderiv ℝ g x) w‖≤2*ε+2*L*δ^2 := by
    simpa only [map_smul,smul_eq_mul,ContinuousLinearMap.sub_apply,Real.norm_eq_abs,
      ←mul_sub,abs_mul,abs_of_pos hδ] using hder
  have he : 2*ε/δ+2*L*δ=(2*ε+2*L*δ^2)/δ := by field_simp
  rw [he]
  apply (le_div_iff₀ hδ).mpr
  convert hh using 1
  · ring

theorem lipschitz_fderiv_of_lipschitz_gradient {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E→ℝ) (L : ℝ≥0) (hL : LipschitzWith L (gradient f)) :
    LipschitzWith L (fderiv ℝ f) := by
  have he : fderiv ℝ f=(InnerProductSpace.toDual ℝ E) ∘ gradient f := by
    funext x
    exact (toDual_gradient (𝕜 := ℝ) (f := f) (x := x)).symm
  rw [he]
  exact (InnerProductSpace.toDual ℝ E).isometry.lipschitz.comp hL |>.weaken (by simp)

theorem norm_gradient_sub_le_of_uniform_sub {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f g : E→ℝ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (L : ℝ≥0)
    (hLf : LipschitzWith L (gradient f)) (hLg : LipschitzWith L (gradient g))
    (ε : ℝ) (hε : 0≤ε) (hb : ∀y,|f y-g y|≤ε)
    (δ : ℝ) (hδ : 0<δ) (x : E) :
    ‖gradient f x-gradient g x‖ ≤ 2*ε/δ+2*L*δ := by
  have he : ‖gradient f x-gradient g x‖=‖fderiv ℝ f x-fderiv ℝ g x‖ := by
    rw [←toDual_gradient (𝕜 := ℝ) (f := f),←toDual_gradient (𝕜 := ℝ) (f := g),←map_sub]
    exact ((InnerProductSpace.toDual ℝ E).norm_map _).symm
  rw [he]
  exact norm_fderiv_sub_le_of_uniform_sub f g hf hg L
    (lipschitz_fderiv_of_lipschitz_gradient f L hLf)
    (lipschitz_fderiv_of_lipschitz_gradient g L hLg) ε hε hb δ hδ x

theorem norm_gradient_sub_le_sqrt_of_uniform_sub {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f g : E→ℝ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (L : ℝ≥0)
    (hLf : LipschitzWith L (gradient f)) (hLg : LipschitzWith L (gradient g))
    (a d : ℝ) (ha : 0≤a) (hd : 0≤d) (hb : ∀y,|f y-g y|≤a*d) (x : E) :
    ‖gradient f x-gradient g x‖≤2*(a+L)*Real.sqrt d := by
  by_cases h0 : d=0
  · have he : f=g := by
      funext y
      have hh := hb y
      rw [h0,mul_zero,abs_nonpos_iff,sub_eq_zero] at hh
      exact hh
    rw [he,sub_self,norm_zero]
    positivity
  · have hdp : 0<d := lt_of_le_of_ne hd (Ne.symm h0)
    have hs := Real.sqrt_pos.mpr hdp
    have hh := norm_gradient_sub_le_of_uniform_sub f g hf hg L hLf hLg (a*d)
      (mul_nonneg ha hd) hb (Real.sqrt d) hs x
    refine hh.trans_eq ?_
    rw [←Real.sq_sqrt hd]
    rw [Real.sqrt_sq hs.le]
    field_simp

end QuantitativePaper
