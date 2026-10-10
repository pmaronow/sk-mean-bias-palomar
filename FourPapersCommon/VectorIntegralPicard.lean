module
public import Mathlib.Analysis.ODE.PicardLindelof
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.Probability.Process.Adapted
public import Mathlib.Tactic

@[expose] public section

/-! Banach-valued integral Picard construction for bounded measurable-time
spatially Lipschitz drifts. The factorial estimate gives existence and
uniqueness without assuming time continuity. -/
noncomputable section
open Function intervalIntegral MeasureTheory Metric Set Filter
open scoped Nat NNReal Topology
namespace FourPapersCommon
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The assumptions needed for an integral equation, allowing discontinuous time dependence. -/
structure IsBoundedVectorDrift (f : ℝ → E → E) (L K : ℝ≥0) : Prop where
  measurable : Measurable (Function.uncurry f)
  norm_le : ∀ t x, ‖f t x‖ ≤ L
  lipschitz : ∀ t, LipschitzWith K (f t)

namespace VectorIntegralPicard
variable {T : ℝ} (hT : 0 ≤ T) (h : E) (L : ℝ≥0)
def zeroTime : Icc (0 : ℝ) T := ⟨0, ⟨le_rfl, hT⟩⟩
abbrev Curve := ODE.FunSpace (zeroTime hT) h 0 L
variable {h L} {K : ℝ≥0} {f : ℝ → E → E}

lemma integrable_comp (hf : IsBoundedVectorDrift f L K) (α : Curve hT h L)
    (t : Icc (0 : ℝ) T) :
    IntervalIntegrable (fun s => f s (α.compProj s)) volume 0 t := by
  apply (intervalIntegrable_const (c := (L : ℝ))).mono_fun'
    (hf.measurable.comp (measurable_id.prodMk α.continuous_compProj.measurable)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun s => hf.norm_le s (α.compProj s))

/-- Picard's integral map on the complete space of bounded-slope curves. -/
def next (hf : IsBoundedVectorDrift f L K) (α : Curve hT h L) : Curve hT h L where
  toFun t := h + ∫ s in 0..t.1, f s (α.compProj s)
  lipschitzWith := LipschitzWith.of_dist_le_mul fun t₁ t₂ => by
    rw [dist_eq_norm, add_sub_add_left_eq_sub,
      integral_interval_sub_left (integrable_comp hT hf α t₁) (integrable_comp hT hf α t₂),
      Subtype.dist_eq, Real.dist_eq]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro s hs
    exact hf.norm_le s _
  mem_closedBall₀ := by simp [zeroTime]

@[simp] lemma next_apply (hf : IsBoundedVectorDrift f L K) (α : Curve hT h L)
    (t : Icc (0 : ℝ) T) : next hT hf α t = h + ∫ s in 0..t.1, f s (α.compProj s) := rfl

lemma dist_comp_iterate_le (hf : IsBoundedVectorDrift f L K)
    (n : ℕ) (t : Icc (0 : ℝ) T) {α γ : Curve hT h L}
    (hh : dist ((next hT hf)^[n] α t) ((next hT hf)^[n] γ t) ≤
      (K * |t.1 - 0|) ^ n / n ! * dist α γ) :
    dist (f t ((next hT hf)^[n] α t)) (f t ((next hT hf)^[n] γ t)) ≤
      K ^ (n + 1) * |t.1 - 0| ^ n / n ! * dist α γ := by
  calc
    _ ≤ K * dist ((next hT hf)^[n] α t) ((next hT hf)^[n] γ t) :=
      (hf.lipschitz t).dist_le_mul _ _
    _ ≤ K ^ (n + 1) * |t.1 - 0| ^ n / n ! * dist α γ := by
      rw [pow_succ', mul_assoc, mul_div_assoc, mul_assoc]
      gcongr
      rwa [← mul_pow]

/-- The genuine factorial estimate for iterated integral Picard maps. -/
lemma dist_iterate_apply_le (hf : IsBoundedVectorDrift f L K)
    (α γ : Curve hT h L) (n : ℕ) (t : Icc (0 : ℝ) T) :
    dist ((next hT hf)^[n] α t) ((next hT hf)^[n] γ t) ≤
      (K * |t.1 - 0|) ^ n / n ! * dist α γ := by
  induction n generalizing t with
  | zero => simpa using!
      ContinuousMap.dist_apply_le_dist (f := ODE.FunSpace.toContinuousMap α) (g := ODE.FunSpace.toContinuousMap γ) t
  | succ n hn =>
    rw [iterate_succ_apply', iterate_succ_apply', dist_eq_norm, next_apply, next_apply,
      add_sub_add_left_eq_sub, ← intervalIntegral.integral_sub
        (integrable_comp hT hf _ t) (integrable_comp hT hf _ t)]
    calc
      _ ≤ ∫ s in uIoc (0 : ℝ) t.1, K ^ (n + 1) * |s - 0| ^ n / n ! * dist α γ := by
        rw [intervalIntegral.norm_intervalIntegral_eq]
        apply MeasureTheory.norm_integral_le_of_norm_le (Continuous.integrableOn_uIoc (by fun_prop))
        apply ae_restrict_mem measurableSet_Ioc |>.mono
        intro s hs
        have hs' : s ∈ Icc (0 : ℝ) T :=
          subset_trans uIoc_subset_uIcc (uIcc_subset_Icc ⟨le_rfl, hT⟩ t.2) hs
        rw [← dist_eq_norm, ODE.FunSpace.compProj_of_mem, ODE.FunSpace.compProj_of_mem]
        exact dist_comp_iterate_le hT hf n ⟨s, hs'⟩ (hn _)
      _ ≤ (K * |t.1 - 0|) ^ (n + 1) / (n + 1) ! * dist α γ := by
        apply le_of_abs_le
        rw [← intervalIntegral.abs_intervalIntegral_eq, intervalIntegral.integral_mul_const,
          intervalIntegral.integral_div, intervalIntegral.integral_const_mul, abs_mul, abs_div,
          abs_mul, intervalIntegral.abs_intervalIntegral_eq, integral_pow_abs_sub_uIoc, abs_div,
          abs_pow, abs_pow, abs_dist, NNReal.abs_eq, abs_abs, mul_div, div_div,
          Nat.abs_cast, ← Nat.cast_succ]
        simp only [Nat.abs_cast]
        rw [← Nat.cast_mul, ← Nat.factorial_succ, ← mul_pow]

lemma dist_iterate_le (hf : IsBoundedVectorDrift f L K)
    (α γ : Curve hT h L) (n : ℕ) :
    dist ((next hT hf)^[n] α) ((next hT hf)^[n] γ) ≤
      (K * T) ^ n / n ! * dist α γ := by
  rw [← MetricSpace.isometry_induced ODE.FunSpace.toContinuousMap
    ODE.FunSpace.toContinuousMap.injective |>.dist_eq, ContinuousMap.dist_le]
  · intro t
    apply le_trans (dist_iterate_apply_le hT hf α γ n t)
    gcongr
    simpa only [sub_zero, abs_of_nonneg t.2.1] using t.2.2
  · positivity

lemma exists_contracting_iterate (hf : IsBoundedVectorDrift f L K) :
    ∃ (n : ℕ) (C : ℝ≥0), ContractingWith C (next (h := h) hT hf)^[n] := by
  obtain ⟨n, hn⟩ := FloorSemiring.tendsto_pow_div_factorial_atTop ((K : ℝ) * T)
    |>.eventually (gt_mem_nhds zero_lt_one) |>.exists
  have hC : 0 ≤ ((K : ℝ) * T) ^ n / n ! := by positivity
  exact ⟨n, ⟨_, hC⟩, hn, LipschitzWith.of_dist_le_mul fun α γ => dist_iterate_le hT hf α γ n⟩

/-- A bounded measurable spatially Lipschitz drift has an actual integral solution. -/
theorem exists_fixedPoint (hf : IsBoundedVectorDrift f L K) :
    ∃ α : Curve hT h L, IsFixedPt (next hT hf) α := by
  obtain ⟨n, C, hc⟩ := exists_contracting_iterate (h := h) hT hf
  exact ⟨_, hc.isFixedPt_fixedPoint_iterate⟩

/-- The integral solution is unique in the complete curve space. -/
theorem fixedPoint_unique (hf : IsBoundedVectorDrift f L K)
    {α γ : Curve hT h L} (ha : IsFixedPt (next hT hf) α) (hg : IsFixedPt (next hT hf) γ) :
    α = γ := by
  obtain ⟨n, C, hc⟩ := exists_contracting_iterate (h := h) hT hf
  exact hc.fixedPoint_unique' (ha.iterate n) (hg.iterate n)

/-- The chosen fixed point is an actual bounded-slope solution. -/
def solution (hf : IsBoundedVectorDrift f L K) : Curve hT h L :=
  Classical.choose (exists_fixedPoint (h := h) hT hf)

lemma solution_fixed (hf : IsBoundedVectorDrift f L K) :
    IsFixedPt (next hT hf) (solution (h := h) hT hf) :=
  Classical.choose_spec (exists_fixedPoint (h := h) hT hf)

lemma solution_equation (hf : IsBoundedVectorDrift f L K) (t : Icc (0 : ℝ) T) :
    solution (h := h) hT hf t = h + ∫ s in 0..t.1, f s ((solution (h := h) hT hf).compProj s) := by
  exact (congrArg (fun α : Curve hT h L => α t) (solution_fixed hT hf)).symm

/-- Every continuous solution of the integral equation equals the constructed one. -/
theorem real_solution_unique (hf : IsBoundedVectorDrift f L K)
    (Y : ℝ → E) (hY : Continuous Y)
    (hYe : ∀ t ∈ Icc (0 : ℝ) T, Y t = h + ∫ s in 0..t, f s (Y s)) :
    ∀ t ∈ Icc (0 : ℝ) T, Y t = (solution (h := h) hT hf).compProj t := by
  have hYi (t : Icc (0 : ℝ) T) : IntervalIntegrable (fun s => f s (Y s)) volume 0 t := by
    apply (intervalIntegrable_const (c := (L : ℝ))).mono_fun'
      (hf.measurable.comp (measurable_id.prodMk hY.measurable)).aestronglyMeasurable
    exact Eventually.of_forall (fun s => hf.norm_le s (Y s))
  let α : Curve hT h L := {
    toFun := fun t => Y t
    lipschitzWith := LipschitzWith.of_dist_le_mul fun t₁ t₂ => by
      rw [hYe t₁ t₁.2, hYe t₂ t₂.2, dist_eq_norm, add_sub_add_left_eq_sub,
        integral_interval_sub_left (hYi t₁) (hYi t₂), Subtype.dist_eq, Real.dist_eq]
      exact intervalIntegral.norm_integral_le_of_norm_le_const (fun s _ => hf.norm_le s (Y s))
    mem_closedBall₀ := by simp [zeroTime, hYe 0 ⟨le_rfl, hT⟩] }
  have haf : IsFixedPt (next hT hf) α := by
    apply ODE.FunSpace.ext
    intro t
    change h + (∫ s in 0..t.1, f s (α.compProj s)) = Y t
    rw [hYe t t.2]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Icc (0 : ℝ) T :=
      (uIcc_subset_Icc ⟨le_rfl, hT⟩ t.2) hs
    dsimp only
    rw [ODE.FunSpace.compProj_of_mem hs']
  have he : α = solution (h := h) hT hf := fixedPoint_unique hT hf haf (solution_fixed hT hf)
  intro t ht
  rw [ODE.FunSpace.compProj_of_mem ht]
  exact congrArg (fun γ : Curve hT h L => γ ⟨t, ht⟩) he

end VectorIntegralPicard
end FourPapersCommon
