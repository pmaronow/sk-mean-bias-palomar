module
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

/-! A C¹ compact cutoff for the dimension-independent Gaussian curvature
argument. Its derivative bound gives the needed mean estimate directly;
the cutoff need not equal one on a whole interval. -/
noncomputable section
open Set Filter
open scoped Topology
namespace FourPapersCommon
set_option maxHeartbeats 800000

def curvatureCutoffUnit (x : ℝ) : ℝ := if |x| ≤ 1 then (1-x^2)^2 else 0

def curvatureCutoffUnitDerivative (x : ℝ) : ℝ := -4*x*max 0 (1-x^2)

theorem curvatureCutoffUnit_eq (x : ℝ) :
    curvatureCutoffUnit x = (max 0 (1-x^2))^2 := by
  by_cases hx : |x| ≤ 1
  · have hs : 0 ≤ 1-x^2 := by nlinarith [sq_le_sq₀ (abs_nonneg x) (show (0:ℝ)≤1 by norm_num) |>.mpr hx,sq_abs x]
    simp [curvatureCutoffUnit,hx,max_eq_right hs]
  · have hs : 1-x^2 ≤ 0 := by
      have hh : 1 < |x| := lt_of_not_ge hx
      nlinarith [sq_abs x]
    simp [curvatureCutoffUnit,hx,max_eq_left hs]

theorem curvatureCutoffUnit_bounds (x : ℝ) :
    0 ≤ curvatureCutoffUnit x ∧ curvatureCutoffUnit x ≤ 1 := by
  rw [curvatureCutoffUnit_eq]
  have hh : 0 ≤ max 0 (1-x^2) := le_max_left _ _
  have hu : max 0 (1-x^2) ≤ 1 := max_le (by norm_num) (by nlinarith [sq_nonneg x])
  exact ⟨sq_nonneg _,by nlinarith⟩

theorem hasDerivAt_curvatureCutoffUnit (x : ℝ) :
    HasDerivAt curvatureCutoffUnit (curvatureCutoffUnitDerivative x) x := by
  have hp (y : ℝ) : HasDerivAt (fun z : ℝ => (1-z^2)^2) (-4*y*(1-y^2)) y := by
    have hd := (((hasDerivAt_id y).pow 2).const_sub 1).pow 2
    simp only [Pi.pow_apply,id_eq,Nat.reduceSub,Nat.cast_ofNat,pow_one,mul_one] at hd
    convert hd using 1 <;> ring
  have hinside (y : ℝ) (hy : y∈Icc (-1:ℝ) 1) : HasDerivWithinAt curvatureCutoffUnit
      (-4*y*(1-y^2)) (Icc (-1:ℝ) 1) y := by
    apply (hp y).hasDerivWithinAt.congr
    · intro z hz
      simp [curvatureCutoffUnit,abs_le.mpr hz]
    · simp [curvatureCutoffUnit,abs_le.mpr hy]
  by_cases hx : |x| < 1
  · have he : curvatureCutoffUnit =ᶠ[𝓝 x] (fun z : ℝ => (1-z^2)^2) := by
      filter_upwards [((continuous_abs.continuousAt).eventually (gt_mem_nhds hx))] with z hz
      simp [curvatureCutoffUnit,hz.le]
    have hs : 0 ≤ 1-x^2 := by nlinarith [sq_le_sq₀ (abs_nonneg x) (show (0:ℝ)≤1 by norm_num) |>.mpr hx.le,sq_abs x]
    simpa [curvatureCutoffUnitDerivative,max_eq_right hs] using (hp x).congr_of_eventuallyEq he
  · by_cases heq : |x| = 1
    · rcases abs_eq (by norm_num : (0:ℝ) ≤ 1) |>.mp heq with h | h
      · subst x
        have ho : HasDerivWithinAt curvatureCutoffUnit 0 (Ici (1:ℝ)) 1 := by
          apply (hasDerivAt_const (1:ℝ) (0:ℝ)).hasDerivWithinAt.congr
          · intro z hz
            change 1≤z at hz
            by_cases hz1 : z=1
            · simp [hz1,curvatureCutoffUnit]
            · have hzlt : 1<z := lt_of_le_of_ne hz (Ne.symm hz1)
              have ha : 1 < |z| := by rw [abs_of_nonneg (by linarith)];exact hzlt
              simp [curvatureCutoffUnit,not_le.mpr ha]
          · simp [curvatureCutoffUnit]
        have hi : HasDerivWithinAt curvatureCutoffUnit 0 (Icc (-1:ℝ) 1) 1 := by
          simpa using hinside 1 (by norm_num)
        have hh := hi.union ho
        have hset : Icc (-1:ℝ) 1 ∪ Ici 1 = Ici (-1:ℝ) := by
          ext y; simp only [mem_union,mem_Icc,mem_Ici]; constructor
          · intro hy; rcases hy with hy | hy
            · exact hy.1
            · linarith
          · intro hy; by_cases hz : y≤1
            · exact Or.inl ⟨hy,hz⟩
            · exact Or.inr (le_of_not_ge hz)
        rw [hset] at hh
        simpa [curvatureCutoffUnitDerivative] using hh.hasDerivAt (Ici_mem_nhds (by norm_num))
      · subst x
        have ho : HasDerivWithinAt curvatureCutoffUnit 0 (Iic (-1:ℝ)) (-1) := by
          apply (hasDerivAt_const (-1:ℝ) (0:ℝ)).hasDerivWithinAt.congr
          · intro z hz
            change z≤ -1 at hz
            by_cases hz1 : z = -1
            · simp [hz1,curvatureCutoffUnit]
            · have hzlt : z < -1 := lt_of_le_of_ne hz hz1
              have ha : 1 < |z| := by rw [abs_of_nonpos (by linarith)];linarith
              simp [curvatureCutoffUnit,not_le.mpr ha]
          · simp [curvatureCutoffUnit]
        have hi : HasDerivWithinAt curvatureCutoffUnit 0 (Icc (-1:ℝ) 1) (-1) := by
          simpa using hinside (-1) (by norm_num)
        have hh := ho.union hi
        have hset : Iic (-1:ℝ) ∪ Icc (-1) 1 = Iic (1:ℝ) := by
          ext y; simp only [mem_union,mem_Icc,mem_Iic]; constructor
          · intro hy; rcases hy with hy | hy
            · linarith
            · exact hy.2
          · intro hy; by_cases hz : y≤ -1
            · exact Or.inl hz
            · exact Or.inr ⟨le_of_not_ge hz,hy⟩
        rw [hset] at hh
        simpa [curvatureCutoffUnitDerivative] using hh.hasDerivAt (Iic_mem_nhds (by norm_num))
    · have hx1 : 1 < |x| := lt_of_le_of_ne (le_of_not_gt hx) (Ne.symm heq)
      have he : curvatureCutoffUnit =ᶠ[𝓝 x] (fun _ : ℝ => 0) := by
        filter_upwards [(continuous_abs.continuousAt.eventually (lt_mem_nhds hx1))] with z hz
        simp [curvatureCutoffUnit,not_le.mpr hz]
      have hs : 1-x^2 ≤ 0 := by nlinarith [sq_abs x]
      simpa [curvatureCutoffUnitDerivative,max_eq_left hs] using
        (hasDerivAt_const x (0:ℝ)).congr_of_eventuallyEq he

theorem contDiff_curvatureCutoffUnit : ContDiff ℝ 1 curvatureCutoffUnit := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun x => (hasDerivAt_curvatureCutoffUnit x).differentiableAt,?_⟩
  have he : deriv curvatureCutoffUnit = curvatureCutoffUnitDerivative :=
    funext (fun x => (hasDerivAt_curvatureCutoffUnit x).deriv)
  rw [he]
  unfold curvatureCutoffUnitDerivative
  fun_prop

theorem curvatureCutoffUnit_derivative_bound (x : ℝ) :
    |curvatureCutoffUnitDerivative x| ≤ 2 := by
  by_cases hx : |x| ≤ 1
  · have hs : 0 ≤ 1-x^2 := by nlinarith [sq_le_sq₀ (abs_nonneg x) (show (0:ℝ)≤1 by norm_num) |>.mpr hx,sq_abs x]
    rw [curvatureCutoffUnitDerivative,max_eq_right hs,abs_mul,abs_mul]
    simp only [abs_of_nonneg hs,abs_neg,abs_of_nonneg (show (0:ℝ)≤4 by norm_num)]
    have h1 : 2 * |x| * (1-x^2) ≤ 1 := by
      have hh := mul_nonneg (sq_nonneg (1-|x|)) hs
      nlinarith [sq_abs x,sq_nonneg (x^2)]
    nlinarith
  · have hs : 1-x^2 ≤ 0 := by
      have hh : 1 < |x| := lt_of_not_ge hx
      nlinarith [sq_abs x]
    simp [curvatureCutoffUnitDerivative,max_eq_left hs]

def curvatureCutoff (R x : ℝ) : ℝ := curvatureCutoffUnit (x/(2*R))

theorem contDiff_curvatureCutoff (R : ℝ) : ContDiff ℝ 1 (curvatureCutoff R) := by
  exact contDiff_curvatureCutoffUnit.comp (contDiff_id.div_const _)

theorem curvatureCutoff_bounds (R x : ℝ) :
    0 ≤ curvatureCutoff R x ∧ curvatureCutoff R x ≤ 1 := curvatureCutoffUnit_bounds _

theorem curvatureCutoff_even (R x : ℝ) : curvatureCutoff R (-x)=curvatureCutoff R x := by
  simp [curvatureCutoff,curvatureCutoffUnit,neg_div]

theorem curvatureCutoff_zero (R : ℝ) : curvatureCutoff R 0=1 := by
  simp [curvatureCutoff,curvatureCutoffUnit]

theorem curvatureCutoff_derivative_bound {R : ℝ} (hR : 0<R) (x : ℝ) :
    |deriv (curvatureCutoff R) x| ≤ 1/R := by
  have hd := (hasDerivAt_curvatureCutoffUnit (x/(2*R))).comp x
    ((hasDerivAt_id x).div_const (2*R))
  rw [show deriv (curvatureCutoff R) x=curvatureCutoffUnitDerivative (x/(2*R))*(1/(2*R))
    from hd.deriv]
  rw [abs_mul,abs_of_pos (by positivity : 0<(1/(2*R):ℝ))]
  apply (mul_le_mul_of_nonneg_right (curvatureCutoffUnit_derivative_bound _) (by positivity)).trans_eq
  field_simp

theorem curvatureCutoff_lower {R : ℝ} (hR : 0<R) (x : ℝ) :
    1-|x|/R ≤ curvatureCutoff R x := by
  have hl := (convex_univ : Convex ℝ (univ: Set ℝ)).norm_image_sub_le_of_norm_deriv_le
    (fun y _ => ((contDiff_curvatureCutoff R).differentiable (by simp)) y)
    (fun y _ => by simpa only [Real.norm_eq_abs] using curvatureCutoff_derivative_bound hR y)
    (mem_univ 0) (mem_univ x)
  rw [Real.norm_eq_abs,curvatureCutoff_zero,Real.norm_eq_abs] at hl
  have hh := neg_abs_le (curvatureCutoff R x-1)
  simp only [sub_zero] at hl
  rw [one_div_mul_eq_div] at hl
  linarith

theorem curvatureCutoff_support {R : ℝ} (hR : 0<R) {x : ℝ}
    (hx : curvatureCutoff R x ≠ 0) : |x| ≤ 2*R := by
  have hs : |x/(2*R)| ≤ 1 := by
    by_contra hn
    exact hx (by simp [curvatureCutoff,curvatureCutoffUnit,hn])
  rw [abs_div,abs_of_pos (by positivity : 0<(2*R:ℝ))] at hs
  exact (div_le_iff₀ (by positivity : 0<(2*R:ℝ))).mp hs |>.trans_eq (one_mul _)

end FourPapersCommon
