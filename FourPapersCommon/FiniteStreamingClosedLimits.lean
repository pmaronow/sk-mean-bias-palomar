module
public import FourPapersCommon.FiniteStreamingPolynomialsIterated
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.UniformSpace.Equicontinuity
public import Mathlib.Topology.UniformSpace.Ascoli
public import Mathlib.Analysis.Normed.Affine.Convex
public import FourPapersCommon.UniformSlopeLimit

@[expose] public section

/-! Closed-interval derivative interpolation.  The actual physical functions
need only be differentiable within the closed interval; no extension through
the model's outside-interval fallback is assumed. -/
noncomputable section
open Set Filter
open scoped Topology NNReal
namespace FourPapersCommon
set_option maxHeartbeats 800000

theorem firstTaylor_remainder_on_convex (f D : ℝ → ℝ) (S : Set ℝ)
    (hS : Convex ℝ S) (hD : ∀ z ∈ S, HasDerivWithinAt f (D z) S z)
    (L : ℝ≥0) (hL : LipschitzOnWith L D S) (x y : ℝ) (hx : x ∈ S) (hy : y ∈ S) :
    |f y - f x - D x * (y - x)| ≤ L * |y - x|^2 := by
  have hsub : segment ℝ x y ⊆ S := hS.segment_subset hx hy
  have hd (z : ℝ) (hz : z ∈ segment ℝ x y) :
      HasDerivWithinAt (fun w => f w - D x * w) (D z - D x) (segment ℝ x y) z := by
    simpa only [mul_one, id_eq] using
      ((hD z (hsub hz)).mono hsub).fun_sub ((hasDerivWithinAt_id z _).const_mul (D x))
  have hb (z : ℝ) (hz : z ∈ segment ℝ x y) : ‖D z - D x‖ ≤ L * |y - x| := by
    have hg := dist_add_dist_of_mem_segment hz
    have hzdist : dist z x ≤ dist y x := by
      rw [dist_comm z x, dist_comm y x]
      linarith [dist_nonneg (x := z) (y := y)]
    have hl := hL.dist_le_mul z (hsub hz) x hx
    rw [dist_eq_norm] at hl
    exact hl.trans (mul_le_mul_of_nonneg_left (by
      simpa only [Real.dist_eq] using hzdist) L.coe_nonneg)
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (convex_segment x y)
    (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  simpa only [Real.norm_eq_abs, show (f y - D x * y) - (f x - D x * x) =
    f y - f x - D x * (y - x) by ring, pow_two, mul_assoc] using hh

theorem derivative_sub_le_on_Icc (f g D E : ℝ → ℝ)
    (hf : ∀ z ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (D z) (Icc 0 1) z)
    (hg : ∀ z ∈ Icc (0 : ℝ) 1, HasDerivWithinAt g (E z) (Icc 0 1) z)
    (L : ℝ≥0) (hD : LipschitzOnWith L D (Icc 0 1))
    (hE : LipschitzOnWith L E (Icc 0 1))
    (ε : ℝ) (hb : ∀ z ∈ Icc (0 : ℝ) 1, |f z - g z| ≤ ε)
    (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1/2) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    |D x - E x| ≤ 2*ε/δ + 2*L*δ := by
  let y := if x ≤ 1/2 then x + δ else x - δ
  have hy : y ∈ Icc (0 : ℝ) 1 := by
    dsimp only [y]; split_ifs <;> constructor <;> linarith [hx.1, hx.2]
  have hxy : |y-x| = δ := by
    dsimp only [y]; split_ifs
    · simp [abs_of_pos hδ]
    · have he : x - δ - x = -δ := by ring
      rw [he, abs_neg, abs_of_pos hδ]
  have htf := firstTaylor_remainder_on_convex f D (Icc 0 1) (convex_Icc _ _) hf L hD x y hx hy
  have htg := firstTaylor_remainder_on_convex g E (Icc 0 1) (convex_Icc _ _) hg L hE x y hx hy
  rw [hxy] at htf htg
  have hv : |(f y-f x)-(g y-g x)| ≤ 2*ε := by
    calc
      _ = |(f y-g y)-(f x-g x)| := by congr 1; ring
      _ ≤ |f y-g y| + |f x-g x| := abs_sub _ _
      _ ≤ 2*ε := by linarith [hb y hy, hb x hx]
  have hd : |(D x-E x)*(y-x)| ≤ 2*ε+2*L*δ^2 := by
    calc
      _ = |((f y-f x)-(g y-g x))-(f y-f x-D x*(y-x))+
        (g y-g x-E x*(y-x))| := by congr 1; ring
      _ ≤ |(f y-f x)-(g y-g x)| + |f y-f x-D x*(y-x)| +
        |g y-g x-E x*(y-x)| :=
        (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ _ := by linarith
  rw [abs_mul, hxy] at hd
  apply (le_div_iff₀ hδ).mpr at hd
  convert hd using 1 <;> field_simp <;> ring

theorem tendstoUniformlyOn_compact_of_pointwise_lipschitzOn (f : ℕ → ℝ → ℝ)
    (g : ℝ → ℝ) (K : ℝ≥0) (S : Set ℝ) (hS : IsCompact S)
    (hK : ∀ j, LipschitzOnWith K (f j) S)
    (hp : ∀ x ∈ S, Tendsto (fun j => f j x) atTop (𝓝 (g x))) :
    TendstoUniformlyOn f g atTop S := by
  haveI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let H := fun j (x : S) => f j x
  have hHL (j : ℕ) : LipschitzWith K (H j) := (hK j).to_restrict
  have he := (LipschitzWith.uniformEquicontinuous H K hHL).equicontinuous
  have ht := (he.tendsto_uniformFun_iff_pi atTop (fun x : S => g x)).mpr
    (tendsto_pi_nhds.mpr fun x => hp x x.property)
  exact tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
    (UniformFun.tendsto_iff_tendstoUniformly.mp ht)

end FourPapersCommon
