module
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawProperties
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingTerminalDefectTests

@[expose] public section

/-! Literal physical tags on the actual observed source forest are jointly
measurable. Their envelope follows from each actual defect being at most two;
unary observation clocks need only be measurable. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n m d : ℕ}

theorem measurable_cavityGeneratedObservedRawPairDefect
    (W : CavityGeneratedObservedRawForest m) (t : CavityGeneratedObservedRawPair W) :
    Measurable (fun z : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree =>
        cavityGeneratedObservedRawPairDefect W t z.1 z.2) := by
  apply measurable_from_prod_countable_left
  intro σ
  have hm := (continuous_cavitySpinOverlapDefect_clock
    (fun q : Paper.Overlap => q) continuous_id
    (observationTerminalSpin (W.tree t.component) t.first (σ t.component))
    (observationTerminalSpin (W.tree t.component) t.second (σ t.component))).measurable
  exact hm.comp (W.measurable_clock t.component _)

theorem cavityGeneratedObservedRawPairDefect_abs_le_two
    (W : CavityGeneratedObservedRawForest m) (t : CavityGeneratedObservedRawPair W)
    (h : CavityGeneratedHistory Paper.Overlap m)
    (σ : CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree) :
    |cavityGeneratedObservedRawPairDefect W t h σ| ≤ 2 :=
  cavitySpinOverlapDefect_abs_le_two n _ (W.clock h t.component _).property _ _

theorem measurable_cavityGeneratedObservedRawTaggedValue
    (W : CavityGeneratedObservedRawForest m) (A : CavityGeneratedObservedRawTaggedTest n W d)
    (hA : Measurable A.base) : Measurable (cavityGeneratedObservedRawTaggedValue W A) := by
  exact hA.mul (Finset.measurable_prod Finset.univ
    (fun i _=>measurable_cavityGeneratedObservedRawPairDefect W (A.pairs i)))

theorem cavityGeneratedObservedRawTaggedValue_abs_le
    (W : CavityGeneratedObservedRawForest m) (A : CavityGeneratedObservedRawTaggedTest n W d)
    (L : ℝ) (hL : 0≤L) (hA : ∀z,|A.base z|≤L)
    (z : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree) :
    |cavityGeneratedObservedRawTaggedValue W A z| ≤ L*2^d := by
  unfold cavityGeneratedObservedRawTaggedValue
  rw [abs_mul,Finset.abs_prod]
  have hp : (∏i : Fin d,|cavityGeneratedObservedRawPairDefect W (A.pairs i) z.1 z.2|) ≤
      ∏i : Fin d,(2:ℝ) :=
    Finset.prod_le_prod₀ (fun i _=>abs_nonneg _) (fun i _=>
      cavityGeneratedObservedRawPairDefect_abs_le_two W (A.pairs i) z.1 z.2)
  simpa using mul_le_mul (hA z) hp (Finset.prod_nonneg fun i _=>abs_nonneg _) hL

end QuantitativeFollowup
