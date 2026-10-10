module
public import QuantitativeFollowup.ConcentratingBump
public import Mathlib.Topology.MetricSpace.Lipschitz

@[expose] public section

/-! Genuine C1,1 regularity of the concentrating bump. Its first
derivative is a polynomial composed with the actual unit-interval clamp;
the a.e. second derivative excludes only the two boundary points. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000

def concentratingFirstPolynomial (y : ℝ) : ℝ := 32*y*(1-y)*(1-2*y)
def concentratingSecondPolynomial (y : ℝ) : ℝ := 32*(1-6*y+6*y^2)
def concentratingUnitClamp (y : ℝ) : ℝ := max 0 (min 1 y)

theorem hasDerivAt_concentratingFirstPolynomial (y : ℝ) :
    HasDerivAt concentratingFirstPolynomial (concentratingSecondPolynomial y) y := by
  have hd := (((hasDerivAt_id y).const_mul 32).mul ((hasDerivAt_id y).const_sub 1)).mul
    (((hasDerivAt_id y).const_mul 2).const_sub 1)
  convert hd using 1
  · funext z
    dsimp only [concentratingFirstPolynomial,id_eq,Pi.mul_apply]
  · dsimp only [concentratingSecondPolynomial,id_eq,Pi.mul_apply]
    ring

theorem concentratingSecondPolynomial_bound (y : ℝ) (hy : y∈Icc (0 : ℝ) 1) :
    |concentratingSecondPolynomial y|≤32 := by
  rw [concentratingSecondPolynomial,abs_le]
  constructor <;> nlinarith [sq_nonneg (y-1/2),mul_nonneg hy.1 (sub_nonneg.mpr hy.2)]

theorem concentratingBumpDerivative_zero_outside (y : ℝ) (hy : y∉Ioo (0 : ℝ) 1) :
    concentratingBumpDerivative y=0 := by
  by_cases hunit : y∈Icc (0 : ℝ) 1
  · rw [concentratingBumpDerivative_eq_on_unit y hunit]
    have he : y=0 ∨ y=1 := by
      by_cases hz : y=0
      · exact Or.inl hz
      · right
        exact le_antisymm hunit.2 (le_of_not_gt (fun hh => hy ⟨lt_of_le_of_ne hunit.1 (Ne.symm hz),hh⟩))
    rcases he with rfl | rfl <;> norm_num
  · have ht : 1-(2*y-1)^2≤0 := by
      have he : y<0 ∨ 1<y := by
        by_cases hz : y<0
        · exact Or.inl hz
        · exact Or.inr (lt_of_not_ge (fun hh => hunit ⟨le_of_not_gt hz,hh⟩))
      rcases he with he | he <;> nlinarith
    simp only [concentratingBumpDerivative,FourPapersCommon.curvatureCutoffUnitDerivative,max_eq_left ht,mul_zero]

theorem concentratingUnitClamp_mem (y : ℝ) : concentratingUnitClamp y∈Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _,max_le zero_le_one (min_le_left _ _)⟩

theorem concentratingBumpDerivative_eq_clamped (y : ℝ) :
    concentratingBumpDerivative y=concentratingFirstPolynomial (concentratingUnitClamp y) := by
  by_cases hy : y∈Icc (0 : ℝ) 1
  · simp only [concentratingUnitClamp,min_eq_right hy.2,max_eq_right hy.1]
    exact concentratingBumpDerivative_eq_on_unit y hy
  · rw [concentratingBumpDerivative_zero_outside y (fun hh => hy ⟨hh.1.le,hh.2.le⟩)]
    by_cases hz : y≤0
    · have he : concentratingUnitClamp y=0 := by
        unfold concentratingUnitClamp
        rw [min_eq_right (hz.trans zero_le_one),max_eq_left hz]
      simp only [he,concentratingFirstPolynomial,mul_zero,zero_mul]
    · have h1 : 1≤y := by
        exact le_of_not_gt (fun hh => hy ⟨(lt_of_not_ge hz).le,hh.le⟩)
      simp only [concentratingUnitClamp,min_eq_left h1,max_eq_right zero_le_one,
        concentratingFirstPolynomial,sub_self,mul_zero,zero_mul]

theorem lipschitz_concentratingBumpDerivative :
    LipschitzWith 32 concentratingBumpDerivative := by
  have hclamp : LipschitzWith 1 concentratingUnitClamp :=
    (LipschitzWith.id.const_min 1).const_max 0
  have hpoly : ∀x∈Icc (0 : ℝ) 1, HasDerivWithinAt concentratingFirstPolynomial
      (concentratingSecondPolynomial x) (Icc (0 : ℝ) 1) x :=
    fun x _ => (hasDerivAt_concentratingFirstPolynomial x).hasDerivWithinAt
  have hb : ∀x∈Icc (0 : ℝ) 1, ‖concentratingSecondPolynomial x‖≤32 :=
    fun x hx => by simpa only [Real.norm_eq_abs] using concentratingSecondPolynomial_bound x hx
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq,Real.dist_eq,concentratingBumpDerivative_eq_clamped x,concentratingBumpDerivative_eq_clamped y]
  have hp := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le hpoly hb
    (concentratingUnitClamp_mem y) (concentratingUnitClamp_mem x)
  have hc := hclamp.dist_le_mul x y
  simp only [Real.norm_eq_abs] at hp
  simp only [Real.dist_eq,NNReal.coe_one,one_mul] at hc
  exact hp.trans (mul_le_mul_of_nonneg_left hc (by norm_num))

theorem concentratingBump_second_derivative_ae :
    (deriv (deriv concentratingBump)) =ᵐ[volume]
      (Ioo (0 : ℝ) 1).indicator concentratingSecondPolynomial := by
  rw [deriv_concentratingBump]
  filter_upwards [volume.ae_ne (0 : ℝ),volume.ae_ne (1 : ℝ)] with y hy0 hy1
  by_cases hy : y∈Ioo (0 : ℝ) 1
  · rw [indicator_of_mem hy]
    have hd := hasDerivAt_concentratingFirstPolynomial y
    have he : concentratingBumpDerivative =ᶠ[𝓝 y] concentratingFirstPolynomial := by
      filter_upwards [isOpen_Ioo.mem_nhds hy] with z hz
      exact concentratingBumpDerivative_eq_on_unit z ⟨hz.1.le,hz.2.le⟩
    exact (hd.congr_of_eventuallyEq he).deriv
  · rw [indicator_of_notMem hy]
    have he : concentratingBumpDerivative =ᶠ[𝓝 y] (fun _ : ℝ => 0) := by
      by_cases hz : y<0
      · filter_upwards [isOpen_Iio.mem_nhds hz] with z hz'
        exact concentratingBumpDerivative_zero_outside z (fun hh => (not_lt_of_ge hz'.le) hh.1)
      · have hypos : 0<y := lt_of_le_of_ne (le_of_not_gt hz) hy0.symm
        have h1 : 1<y := lt_of_le_of_ne (le_of_not_gt (fun hh => hy ⟨hypos,hh⟩)) hy1.symm
        filter_upwards [isOpen_Ioi.mem_nhds h1] with z hz'
        exact concentratingBumpDerivative_zero_outside z (fun hh => (not_lt_of_ge hz'.le) hh.2)
    exact ((hasDerivAt_const y (0 : ℝ)).congr_of_eventuallyEq he).deriv

theorem concentratingBump_second_derivative_bound_ae :
    ∀ᵐy∂volume, |deriv (deriv concentratingBump) y|≤32 := by
  filter_upwards [concentratingBump_second_derivative_ae] with y hy
  rw [hy]
  by_cases hunit : y∈Ioo (0 : ℝ) 1
  · rw [indicator_of_mem hunit]
    exact concentratingSecondPolynomial_bound y ⟨hunit.1.le,hunit.2.le⟩
  · rw [indicator_of_notMem hunit]
    norm_num

end QuantitativeFollowup
