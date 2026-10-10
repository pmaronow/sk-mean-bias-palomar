module
public import FourPapersCommon.ExpandingSmoothCutoff
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

@[expose] public section

/-! Uniform jet estimates and local derivative convergence of compactly
localized exponential-growth functions. All cutoffs are genuine smooth
functions, and no dominated-convergence or Itô conclusion is assumed. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace FourPapersCommon
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 64
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [HasContDiffBump E]

def expandingCutoffJetConstant (r : ℕ) : ℝ:=
  (norm_iteratedFDeriv_expandingSmoothCutoff_le (E := E) r).choose

theorem expandingCutoffJetConstant_pos (r : ℕ) :
    0<expandingCutoffJetConstant (E := E) r:=
  (norm_iteratedFDeriv_expandingSmoothCutoff_le (E := E) r).choose_spec.1

theorem norm_iteratedFDeriv_expandingSmoothCutoff_le_constant (r j : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ r (expandingSmoothCutoff j) x‖≤
      expandingCutoffJetConstant (E := E) r := by
  have h:=(norm_iteratedFDeriv_expandingSmoothCutoff_le (E := E) r).choose_spec.2 j x
  have hp : 1≤((j : ℝ)+1)^r:=one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) j] : 1≤(j : ℝ)+1)
  exact h.trans (div_le_self (expandingCutoffJetConstant_pos r).le hp)

def localizedSmoothFunction (j : ℕ) (f : E→ℝ) : E→ℝ:=
  fun x=>expandingSmoothCutoff j x*f x

theorem contDiff_localizedSmoothFunction (j : ℕ) (f : E→ℝ)
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (localizedSmoothFunction j f):=
  (contDiff_expandingSmoothCutoff j).mul hf

theorem hasCompactSupport_localizedSmoothFunction (j : ℕ) (f : E→ℝ) :
    HasCompactSupport (localizedSmoothFunction j f):=
  (hasCompactSupport_expandingSmoothCutoff j).mul_right

def localizedJetCoefficient (r : ℕ) : ℝ:=
  ∑i∈Finset.range (r+1),(r.choose i : ℝ)*expandingCutoffJetConstant (E := E) i

theorem localizedJetCoefficient_nonneg (r : ℕ) :
    0≤localizedJetCoefficient (E := E) r := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (Nat.cast_nonneg _) (expandingCutoffJetConstant_pos i).le

theorem norm_iteratedFDeriv_localizedSmoothFunction_exponential_le
    (j r : ℕ) (f : E→ℝ) (hf : ContDiff ℝ ∞ f) (B K : ℝ) (hB : 0≤B)
    (x : E) (hbound : ∀i : ℕ,i≤r→‖iteratedFDeriv ℝ i f x‖≤B*Real.exp (K*‖x‖)) :
    ‖iteratedFDeriv ℝ r (localizedSmoothFunction j f) x‖≤
      localizedJetCoefficient (E := E) r*(B*Real.exp (K*‖x‖)) := by
  apply (norm_iteratedFDeriv_mul_le (contDiff_expandingSmoothCutoff j) hf x (by simp)).trans
  rw [localizedJetCoefficient,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left
      (norm_iteratedFDeriv_expandingSmoothCutoff_le_constant i j x) (Nat.cast_nonneg _)
  · exact hbound (r-i) (Nat.sub_le _ _)
  · exact norm_nonneg _
  · exact mul_nonneg (Nat.cast_nonneg _) (expandingCutoffJetConstant_pos i).le

theorem norm_iteratedFDeriv_localizedSmoothFunction_global_le
    (j r : ℕ) (f : E→ℝ) (hf : ContDiff ℝ ∞ f) (B K : ℝ) (hB : 0≤B)
    (hbound : ∀x : E,∀i : ℕ,i≤r→‖iteratedFDeriv ℝ i f x‖≤B*Real.exp (K*‖x‖)) :
    ∀x : E,‖iteratedFDeriv ℝ r (localizedSmoothFunction j f) x‖≤
      localizedJetCoefficient (E := E) r*(B*Real.exp (|K| *(2*((j : ℝ)+1)))) := by
  intro x
  by_cases hx : ‖x‖≤2*((j : ℝ)+1)
  · apply (norm_iteratedFDeriv_localizedSmoothFunction_exponential_le j r f hf B K hB x
      (hbound x)).trans
    apply mul_le_mul_of_nonneg_left _ (localizedJetCoefficient_nonneg r)
    apply mul_le_mul_of_nonneg_left _ hB
    apply Real.exp_le_exp.mpr
    exact (mul_le_mul_of_nonneg_right (le_abs_self K) (norm_nonneg x)).trans
      (mul_le_mul_of_nonneg_left hx (abs_nonneg K))
  · have hs : tsupport (localizedSmoothFunction j f)⊆
        Metric.closedBall (0 : E) (2*((j : ℝ)+1)) := by
      exact tsupport_mul_subset_left.trans (by
        change tsupport (expandingSmoothBump (E := E) j : E→ℝ)⊆_
        rw [(expandingSmoothBump (E := E) j).tsupport_eq]
        rfl)
    have hnot : x∉Function.support (iteratedFDeriv ℝ r (localizedSmoothFunction j f)) := by
      intro he
      have hmem:=hs (support_iteratedFDeriv_subset r he)
      exact hx (by simpa only [Metric.mem_closedBall,dist_zero_right] using hmem)
    rw [Function.notMem_support.mp hnot,norm_zero]
    exact mul_nonneg (localizedJetCoefficient_nonneg r) (mul_nonneg hB (Real.exp_pos _).le)

theorem localizedSmoothFunction_eventually_derivative_eq (r : ℕ) (f : E→ℝ) (x : E) :
    ∀ᶠj : ℕ in atTop,iteratedFDeriv ℝ r (localizedSmoothFunction j f) x=
      iteratedFDeriv ℝ r f x := by
  filter_upwards [expandingSmoothCutoff_eventually_one x] with j hj
  have he:localizedSmoothFunction j f=ᶠ[𝓝 x]f:=by
    filter_upwards [hj] with y hy
    simp only [localizedSmoothFunction,hy,one_mul]
  exact (he.iteratedFDeriv ℝ r).self_of_nhds

end FourPapersCommon
