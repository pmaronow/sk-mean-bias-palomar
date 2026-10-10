module
public import QuantitativeFollowup.FollowupCavityMarkedDefectBounds

@[expose] public section

/-! Positive observables retain their original expectation after genuine
fresh marking. Every defect is bounded independently of dimension. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency true
variable {n k : ℕ}

theorem integral_cavityCrossVertexMarked_defect_abs_le
    (D:AnisotropicSpinModel (n+1))(s:RSBScheme k)(a:ℝ)(T:FiniteTerminalGenealogy (k+2))
    (v w:FiniteCascadeRecordVertex (trimRoot T))(q:ℝ)(hq:q∈Icc (0:ℝ) 1)
    (F:CavityPathRecordSpace (trimRoot T) (n+1)→ℝ)(hF:Measurable F)
    (C:ℝ)(hC:0≤C)(hFb:∀r,|F r|≤C)(hF0:∀r,0≤F r):
    |∫z,F z.1*cavitySpinOverlapDefect n q z.2.1 z.2.2∂anisotropicCrossVertexMarkedLaw D s a T v w|≤
      2*(∫r,F r∂anisotropicTrimmedRecordedTreeLaw D s a T):=by
  exact integral_marked_defect_abs_le_of_fst _ _ (anisotropicCrossVertexMarkedLaw_fst D s a T v w)
    F hF C hC hFb hF0 _
    ((measurable_of_finite (fun z:Configuration (n+1)×Configuration (n+1)=>cavitySpinOverlapDefect n q z.1 z.2)).comp measurable_snd)
    2 (by norm_num) (fun z=>cavitySpinOverlapDefect_abs_le_two n q hq _ _)

theorem integral_cavityFutureVertexMarked_defect_abs_le
    (D:AnisotropicSpinModel (n+1))(s:RSBScheme k)(a:ℝ)(T:FiniteTerminalGenealogy (k+2))
    (v:FiniteCascadeRecordVertex (trimRoot T))(q:Paper.Overlap)
    (F:CavityPathRecordSpace (trimRoot T) (n+1)→ℝ)(hF:Measurable F)
    (C:ℝ)(hC:0≤C)(hFb:∀r,|F r|≤C)(hF0:∀r,0≤F r):
    |∫z,F z.1*cavitySpinOverlapDefect n q z.2.1 z.2.2∂anisotropicFutureVertexMarkedLaw D s a T v q|≤
      2*(∫r,F r∂anisotropicTrimmedRecordedTreeLaw D s a T):=by
  exact integral_marked_defect_abs_le_of_fst _ _ (anisotropicFutureVertexMarkedLaw_fst D s a T v q)
    F hF C hC hFb hF0 _
    ((measurable_of_finite (fun z:Configuration (n+1)×Configuration (n+1)=>cavitySpinOverlapDefect n q z.1 z.2)).comp measurable_snd)
    2 (by norm_num) (fun z=>cavitySpinOverlapDefect_abs_le_two n q q.property _ _)

theorem integral_cavityOriginalVertexMarked_defect_abs_le
    (D:AnisotropicSpinModel (n+1))(s:RSBScheme k)(a:ℝ)(T:FiniteTerminalGenealogy (k+2))
    (v:FiniteCascadeRecordVertex (trimRoot T))
    (F:CavityPathRecordSpace (trimRoot T) (n+1)→ℝ)(hF:Measurable F)
    (C:ℝ)(hC:0≤C)(hFb:∀r,|F r|≤C)(hF0:∀r,0≤F r):
    |∫z,F z.1*cavityOriginalVertexOverlapSum n s T v
      (finiteCascadeRecordTerminalSpins (trimRoot T) z.1.2) z.2∂anisotropicSingleVertexMarkedLaw D s a T v|≤
      (2*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ))*
        (∫r,F r∂anisotropicTrimmedRecordedTreeLaw D s a T):=by
  have hspin:Measurable (fun z:CavityPathRecordSpace (trimRoot T) (n+1)×Configuration (n+1)=>
      (finiteCascadeRecordTerminalSpins (trimRoot T) z.1.2,z.2)):=
    ((measurable_finiteCascadeRecordTerminalSpins _).comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd
  exact integral_marked_defect_abs_le_of_fst _ _ (anisotropicSingleVertexMarkedLaw_fst D s a T v)
    F hF C hC hFb hF0 _
    ((measurable_of_finite (fun z:TerminalSpins (Configuration (n+1)) (trimRoot T)×Configuration (n+1)=>
      cavityOriginalVertexOverlapSum n s T v z.1 z.2)).comp hspin)
    _ (by positivity) (fun z=>cavityOriginalVertexOverlapSum_abs_le n s T v _ _)

theorem cavityNormalizerFreshDefect_abs_le
    (D:AnisotropicSpinModel (n+1))(μ:Paper.ParisiMeasure)(a:ℝ)(ha:a∈Icc (0:ℝ) 1):
    |cavityNormalizerFreshDefect D μ a|≤2*(1-a):=by
  have hb (q:Paper.Overlap):
      ‖∫z,cavitySpinOverlapDefect n q z.2.1 z.2.2∂anisotropicFreshTerminalPairLaw D μ a q‖≤2:=by
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
      (μ:=anisotropicFreshTerminalPairLaw D μ a q) (C:=2)
      (.of_forall fun z=>by simpa only [Real.norm_eq_abs] using cavitySpinOverlapDefect_abs_le_two n q q.property z.2.1 z.2.2)
  have hx:=norm_integral_le_of_norm_le_const (μ:=parisiFreeMeasure μ a) (C:=2) (.of_forall hb)
  change ‖cavityNormalizerFreshDefect D μ a‖≤_ at hx
  rw [Real.norm_eq_abs,Measure.real,parisiFreeMeasure_univ,ENNReal.toReal_ofReal (sub_nonneg.mpr ha.2)] at hx
  exact hx.trans_eq (by ring)

end QuantitativeFollowup
