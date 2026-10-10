module
public import QuantitativeFollowup.ConcentratingBumpRegularity

@[expose] public section

/-! The literal sharp supremum of the quartic bump's first derivative.
The bound is attained at an actual interior point. -/
noncomputable section
open Set
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000

theorem concentratingBumpDerivative_sharp_bound (y : ℝ) :
    |concentratingBumpDerivative y|≤16*Real.sqrt 3/9 := by
  by_cases hy : y∈Icc (0 : ℝ) 1
  · let z := 2*y-1
    have hz : z^2≤1 := by dsimp only [z]; nlinarith [mul_nonneg hy.1 (sub_nonneg.mpr hy.2)]
    have he : concentratingBumpDerivative y= -8*z*(1-z^2) := by
      rw [concentratingBumpDerivative_eq_on_unit y hy]
      dsimp only [z]
      ring
    have hp : 0≤(1-3*z^2)^2*(4-3*z^2) := mul_nonneg (sq_nonneg _) (by linarith)
    have hs : (concentratingBumpDerivative y)^2≤256/27 := by rw [he]; nlinarith [hp]
    have hc : (16*Real.sqrt 3/9)^2=(256/27 : ℝ) := by
      rw [div_pow,mul_pow,Real.sq_sqrt (by norm_num : (0 : ℝ)≤3)]
      norm_num
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity : 0≤16*Real.sqrt 3/9)).mp
    rw [sq_abs,hc]
    exact hs
  · rw [concentratingBumpDerivative_zero_outside y (fun hh => hy ⟨hh.1.le,hh.2.le⟩)]
    rw [abs_zero]
    positivity

theorem concentratingBumpDerivative_attains_bound :
    ∃y∈Ioo (0 : ℝ) 1, concentratingBumpDerivative y=16*Real.sqrt 3/9 := by
  let r := Real.sqrt 3
  let y := (1-r⁻¹)/2
  have hr : 0<r := by dsimp only [r]; positivity
  have hsq : r^2=3 := Real.sq_sqrt (by norm_num)
  have hr1 : 1<r := by nlinarith [hsq]
  have hInv : r⁻¹<1 := by
    exact (inv_lt_one₀ hr).mpr hr1
  have hInv0 : 0<r⁻¹ := inv_pos.mpr hr
  have hy : y∈Ioo (0 : ℝ) 1 := by dsimp only [y]; constructor <;> linarith
  refine ⟨y,hy,?_⟩
  have hz : 2*y-1= -r⁻¹ := by dsimp only [y]; ring
  rw [concentratingBumpDerivative,FourPapersCommon.curvatureCutoffUnitDerivative,hz,neg_sq,inv_pow,hsq]
  norm_num
  change _=16*r/9
  field_simp
  nlinarith [hsq]

theorem concentratingBumpDerivative_sup :
    sSup (Set.range (fun y => |concentratingBumpDerivative y|))=16*Real.sqrt 3/9 := by
  have hb : BddAbove (Set.range (fun y => |concentratingBumpDerivative y|)) :=
    ⟨16*Real.sqrt 3/9,fun z hz => by obtain ⟨y,rfl⟩ := hz; exact concentratingBumpDerivative_sharp_bound y⟩
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    intro z hz
    obtain ⟨y,rfl⟩ := hz
    exact concentratingBumpDerivative_sharp_bound y
  · obtain ⟨y,hy,he⟩ := concentratingBumpDerivative_attains_bound
    apply le_csSup hb
    exact ⟨y,by change |concentratingBumpDerivative y|=16*Real.sqrt 3/9; rw [he,abs_of_nonneg (by positivity)]⟩

theorem concentratingBumpDerivative_sup_lt_four :
    sSup (Set.range (fun y => |concentratingBumpDerivative y|))<4 := by
  rw [concentratingBumpDerivative_sup]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ)≤3)
  have hp := Real.sqrt_nonneg (3 : ℝ)
  nlinarith

end QuantitativeFollowup
