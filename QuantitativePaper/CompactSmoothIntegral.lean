module
public import QuantitativePaper.LocalSmoothIntegral
public import QuantitativePaper.FieldSliceJetContinuity
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-! Jointly smooth functions integrate smoothly over a fixed compact
interval. Local derivative bounds come from actual compact rectangles. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace QuantitativePaper
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem contDiff_compact_parameter_integral (f : ℝ×E→F) (hf : ContDiff ℝ ∞ f)
    (a b : ℝ) : ContDiff ℝ ∞ (fun x=>∫r in Icc a b, f (r,x)) := by
  let S := Icc a b
  let G : E→ℝ→F := fun x r=>S.indicator (fun t=>f (t,x)) r
  have he (j : ℕ) (x : E) (r : ℝ) :
      iteratedFDeriv ℝ j (fun y=>G y r) x=
        S.indicator (fun t=>iteratedFDeriv ℝ j (fun y=>f (t,y)) x) r := by
    by_cases hr : r∈S
    · have hg : (fun y=>G y r)=(fun y=>f (r,y)) := by
        funext y
        exact indicator_of_mem hr _
      rw [hg,indicator_of_mem hr]
    · have hg : (fun y=>G y r)=(fun _=>0) := by
        funext y
        exact indicator_of_notMem hr _
      rw [hg,indicator_of_notMem hr]
      by_cases hj : j=0
      · subst j
        ext v
        simp only [iteratedFDeriv_zero_apply,ContinuousMultilinearMap.zero_apply]
      · rw [iteratedFDeriv_const_of_ne hj]
        rfl
  apply contDiff_infty.mpr
  intro N
  have hGn : ContDiffOn ℝ N (fun x=>∫r,G x r) univ := by
    apply contDiffOn_integral_of_dominated_derivatives N volume G univ isOpen_univ
    · intro r
      by_cases hr : r∈S
      · have hg : (fun x=>G x r)=(fun x=>f (r,x)) := by
          funext x
          exact indicator_of_mem hr _
        rw [hg]
        exact (hf.comp (contDiff_const.prodMk contDiff_id) |>.of_le (by simp)).contDiffOn
      · have hg : (fun x=>G x r)=(fun _=>0) := by
          funext x
          exact indicator_of_notMem hr _
        rw [hg]
        exact contDiffOn_const
    · intro j hj x _
      simp_rw [he]
      exact (((continuous_fieldSlice_iteratedFDeriv f hf j).comp
        (continuous_id.prodMk continuous_const)).stronglyMeasurable.indicator measurableSet_Icc).aestronglyMeasurable
    · intro x _
      have hbnd (j : ℕ) : ∃ C : ℝ, ∀r∈S, ∀y∈Metric.closedBall x 1,
          ‖iteratedFDeriv ℝ j (fun z=>f (r,z)) y‖≤C := by
        obtain ⟨C,hC⟩ := (isCompact_Icc.prod (isCompact_closedBall x 1)).exists_bound_of_continuousOn
          (continuous_fieldSlice_iteratedFDeriv f hf j).continuousOn
        exact ⟨C,fun r hr y hy=>hC (r,y) ⟨hr,hy⟩⟩
      choose C hC using hbnd
      refine ⟨Metric.ball x 1,Metric.ball_mem_nhds x (by norm_num),subset_univ _,
        fun j=>S.indicator (fun _=>C j),?_,?_⟩
      · intro j _
        have hi : IntegrableOn (fun _ : ℝ => C j) S volume :=
          integrableOn_const (by simp [S, Real.volume_Icc])
        exact hi.integrable_indicator measurableSet_Icc
      · intro j hj y hy r
        rw [he]
        dsimp only
        by_cases hr : r∈S
        · simp only [indicator_of_mem hr]
          exact hC j r hr y (Metric.ball_subset_closedBall hy)
        · simp only [indicator_of_notMem hr]
          simp
  have hG : ContDiff ℝ N (fun x=>∫r,G x r) := contDiffOn_univ.mp hGn
  have hh : (fun x=>∫r,G x r)=(fun x=>∫r in Icc a b,f (r,x)) := by
    funext x
    exact integral_indicator measurableSet_Icc
  rwa [hh] at hG

end QuantitativePaper
