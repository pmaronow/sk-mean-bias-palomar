module
public import QuantitativeFollowup.SupportingGeneratedObservedRawFutureForestReceiver
public import QuantitativeFollowup.FollowupCavityGeneratedRawForestHistoryStreamingKernel

@[expose] public section

/-! The actual raw future terminal test retains all old components and
the fresh pair. Its bound and measurability hold for every history,
including outside the source support. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n m : ℕ}

theorem measurable_cavityGeneratedObservedRawFutureTerminalTest
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) (j : Fin (W.depth c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (hF : Measurable F) :
    Measurable (fun z : CavityGeneratedHistory Paper.Overlap (m+2) ×
      CavityGeneratedForestTerminalSample (n:=n)
        (cavityGeneratedObservedRawFutureForest W c γ j).depth
        (cavityGeneratedObservedRawFutureForest W c γ j).tree =>
      cavityGeneratedObservedRawFutureTerminalTest W c γ j F z.1 z.2) := by
  have hb := hF.comp
    ((measurable_cavityGeneratedObservedRawFutureHistoryPrefix.comp measurable_fst).prodMk
      ((measurable_of_finite (cavityGeneratedObservedRawFutureOldTerminal (n:=n) W c γ j)).comp measurable_snd))
  have hd : Measurable (fun z : CavityGeneratedHistory Paper.Overlap (m+2) ×
      CavityGeneratedForestTerminalSample (n:=n)
        (cavityGeneratedObservedRawFutureForest W c γ j).depth
        (cavityGeneratedObservedRawFutureForest W c γ j).tree =>
      cavitySpinOverlapDefect n (z.1 cavityGeneratedObservedRawFutureSecondMark)
        (cavityGeneratedObservedRawFutureChosenTerminal W c γ j z.2).2.1
        (cavityGeneratedObservedRawFutureChosenTerminal W c γ j z.2).2.2) := by
    apply measurable_from_prod_countable_left
    intro σ
    exact (continuous_cavitySpinOverlapDefect_clock (fun r : Paper.Overlap => r) continuous_id
      (cavityGeneratedObservedRawFutureChosenTerminal W c γ j σ).2.1
      (cavityGeneratedObservedRawFutureChosenTerminal W c γ j σ).2.2).measurable.comp
        (measurable_pi_apply cavityGeneratedObservedRawFutureSecondMark)
  exact hb.mul hd

theorem abs_cavityGeneratedObservedRawFutureTerminalTest_le
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) (j : Fin (W.depth c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (L : ℝ) (hL : 0≤L) (hbound : ∀z, |F z|≤L)
    (H : CavityGeneratedHistory Paper.Overlap (m+2))
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedObservedRawFutureForest W c γ j).depth
      (cavityGeneratedObservedRawFutureForest W c γ j).tree) :
    |cavityGeneratedObservedRawFutureTerminalTest W c γ j F H σ|≤2*L := by
  rw [cavityGeneratedObservedRawFutureTerminalTest,abs_mul]
  exact (mul_le_mul (hbound _)
    (cavitySpinOverlapDefect_abs_le_two n _ (H cavityGeneratedObservedRawFutureSecondMark).property _ _)
    (abs_nonneg _) hL).trans_eq (by ring)

def cavityGeneratedObservedRawFutureSuccessorExpectation
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) (j : Fin (W.depth c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (H : CavityGeneratedHistory Paper.Overlap (m+2)) : ℝ :=
  ∫σ, cavityGeneratedObservedRawFutureTerminalTest W c γ j F H σ
    ∂(cavityGeneratedNativeForestTerminalProbability D μ a
      (cavityGeneratedObservedRawFutureForest W c γ j).depth
      (cavityGeneratedObservedRawFutureForest W c γ j).tree
      ((cavityGeneratedObservedRawFutureForest W c γ j).clock H) : Measure _)

theorem measurable_cavityGeneratedObservedRawFutureSuccessorExpectation
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) (j : Fin (W.depth c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (hF : Measurable F) :
    Measurable (cavityGeneratedObservedRawFutureSuccessorExpectation D μ a W c γ j F) := by
  let V := cavityGeneratedObservedRawFutureForest W c γ j
  have hi := (measurable_cavityGeneratedObservedRawFutureTerminalTest W c γ j F hF).stronglyMeasurable.integral_kernel_prod_right'
    (κ:=cavityGeneratedRawForestTerminalKernel D μ a V.depth V.tree V.clock V.measurable_clock V.clock_antitone)
  convert hi.measurable using 1
  funext H
  rw [cavityGeneratedRawForestTerminalKernel_apply]
  rfl

theorem abs_cavityGeneratedObservedRawFutureSuccessorExpectation_le
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) (j : Fin (W.depth c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (L : ℝ) (hL : 0≤L) (hbound : ∀z, |F z|≤L)
    (H : CavityGeneratedHistory Paper.Overlap (m+2)) :
    |cavityGeneratedObservedRawFutureSuccessorExpectation D μ a W c γ j F H|≤2*L := by
  simpa only [cavityGeneratedObservedRawFutureSuccessorExpectation,Real.norm_eq_abs,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const
      (μ:=(cavityGeneratedNativeForestTerminalProbability D μ a
        (cavityGeneratedObservedRawFutureForest W c γ j).depth
        (cavityGeneratedObservedRawFutureForest W c γ j).tree
        ((cavityGeneratedObservedRawFutureForest W c γ j).clock H) : Measure _))
      (f:=cavityGeneratedObservedRawFutureTerminalTest W c γ j F H) (C:=2*L)
      (.of_forall fun σ => by simpa only [Real.norm_eq_abs] using
        abs_cavityGeneratedObservedRawFutureTerminalTest_le W c γ j F L hL hbound H σ)

end QuantitativeFollowup
