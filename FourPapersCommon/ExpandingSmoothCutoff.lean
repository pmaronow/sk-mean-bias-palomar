module
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Group.Bounded

@[expose] public section

/-! Actual expanding compact smooth cutoffs. Their positive jets are
uniformly bounded by scaled jets of one fixed bump, and each cutoff is
eventually equal to one on a neighbourhood of every fixed point. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace FourPapersCommon
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 64
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [HasContDiffBump E]

def unitCutoff : ContDiffBump (0 : E) := ⟨1,2,by norm_num,by norm_num⟩

def expandingSmoothBump (j : ℕ) : ContDiffBump (0 : E) where
  rIn := (j : ℝ)+1
  rOut := 2*((j : ℝ)+1)
  rIn_pos := by positivity
  rIn_lt_rOut := by nlinarith [Nat.cast_nonneg (α := ℝ) j]

def expandingSmoothCutoff (j : ℕ) : E→ℝ := (expandingSmoothBump (E := E) j : E→ℝ)

theorem contDiff_expandingSmoothCutoff (j : ℕ) :
    ContDiff ℝ ∞ (expandingSmoothCutoff (E := E) j):=
  (expandingSmoothBump (E := E) j).contDiff

theorem hasCompactSupport_expandingSmoothCutoff (j : ℕ) :
    HasCompactSupport (expandingSmoothCutoff (E := E) j):=
  (expandingSmoothBump (E := E) j).hasCompactSupport

theorem expandingSmoothCutoff_mem_Icc (j : ℕ) (x : E) :
    expandingSmoothCutoff j x∈Icc (0 : ℝ) 1:=
  ⟨(expandingSmoothBump (E := E) j).nonneg,(expandingSmoothBump (E := E) j).le_one⟩

theorem expandingSmoothCutoff_eq_scaled (j : ℕ) :
    expandingSmoothCutoff (E := E) j=
      fun x=>(unitCutoff (E := E)) (((j : ℝ)+1)⁻¹ • x) := by
  funext x
  simp only [expandingSmoothCutoff,ContDiffBump.apply,expandingSmoothBump,unitCutoff,
    sub_zero,inv_one,one_smul,div_one]
  congr 2
  have hn : (j : ℝ)+1≠0 := by positivity
  field_simp

theorem expandingSmoothCutoff_eventually_one (x : E) :
    ∀ᶠ j : ℕ in atTop,expandingSmoothCutoff (E := E) j=ᶠ[𝓝 x] (fun _=>1) := by
  obtain ⟨N,hN⟩:=exists_nat_gt ‖x‖
  filter_upwards [eventually_ge_atTop N] with j hj
  apply (expandingSmoothBump (E := E) j).eventuallyEq_one_of_mem_ball
  simpa only [Metric.mem_ball,dist_zero_right,expandingSmoothBump] using
    (show ‖x‖<(j : ℝ)+1 by
      have hh : (N : ℝ)≤j := by exact_mod_cast hj
      linarith)

theorem norm_iteratedFDeriv_expandingSmoothCutoff_le (r : ℕ) :
    ∃C : ℝ,0<C∧∀j : ℕ,∀x : E,
      ‖iteratedFDeriv ℝ r (expandingSmoothCutoff j) x‖≤
        C/((j : ℝ)+1)^r := by
  have hc:HasCompactSupport (iteratedFDeriv ℝ r (unitCutoff (E := E) : E→ℝ)):=
    (unitCutoff (E := E)).hasCompactSupport.iteratedFDeriv r
  have hcont:Continuous (iteratedFDeriv ℝ r (unitCutoff (E := E) : E→ℝ)):=
    ((unitCutoff (E := E)).contDiff (n := (r : ℕ∞))).continuous_iteratedFDeriv le_rfl
  obtain ⟨C,hC,hbound⟩:=hc.isCompact_range hcont |>.isBounded.exists_pos_norm_le
  refine ⟨C,hC,fun j x=>?_⟩
  rw [expandingSmoothCutoff_eq_scaled,
    iteratedFDeriv_comp_const_smul _ ((unitCutoff (E := E)).contDiff (n := r)),norm_smul,
    Real.norm_eq_abs,abs_pow,abs_inv,abs_of_nonneg (by positivity : 0≤(j : ℝ)+1)]
  have hh:=hbound (iteratedFDeriv ℝ r (unitCutoff (E := E) : E→ℝ) (((j : ℝ)+1)⁻¹ • x))
    (mem_range_self _)
  calc
    _ ≤ (((j : ℝ)+1)⁻¹)^r*C := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by rw [inv_pow,div_eq_mul_inv];ring

end FourPapersCommon
