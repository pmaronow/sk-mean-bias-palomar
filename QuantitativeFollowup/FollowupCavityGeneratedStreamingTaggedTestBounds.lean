module
public import QuantitativeFollowup.FollowupCavityGeneratedStreamingTaggedTests
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingTerminalDefectTests

@[expose] public section

/-! Joint measurability and count-only bounds for literal physical tag products. -/
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

theorem measurable_cavityGeneratedForestPairDefect
    (W : CavityGeneratedConstructedForest m) (t : CavityGeneratedForestPair W) :
    Measurable (fun z : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree =>
        cavityGeneratedForestPairDefect n W t z.1 z.2) := by
  apply measurable_from_prod_countable_left
  intro σ
  exact (continuous_cavitySpinOverlapDefect_clock
    (fun h=>W.clockTemplate.clock h t.component _)
    (W.clockTemplate.clock_continuous t.component _)
    (observationTerminalSpin (W.tree t.component) t.first (σ t.component))
    (observationTerminalSpin (W.tree t.component) t.second (σ t.component))).measurable

theorem cavityGeneratedForestPairDefect_abs_le_two
    (W : CavityGeneratedConstructedForest m) (t : CavityGeneratedForestPair W)
    (h : CavityGeneratedHistory Paper.Overlap m)
    (σ : CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree) :
    |cavityGeneratedForestPairDefect n W t h σ| ≤ 2 :=
  cavitySpinOverlapDefect_abs_le_two n _ (W.clockTemplate.clock h t.component _).property _ _

theorem measurable_cavityGeneratedTaggedTestValue
    (W : CavityGeneratedConstructedForest m) (A : CavityGeneratedTaggedTest n W d)
    (hA : Measurable A.base) : Measurable (cavityGeneratedTaggedTestValue W A) := by
  exact hA.mul (Finset.measurable_prod Finset.univ
    (fun i _=>measurable_cavityGeneratedForestPairDefect W (A.pairs i)))

theorem cavityGeneratedTaggedTestValue_abs_le
    (W : CavityGeneratedConstructedForest m) (A : CavityGeneratedTaggedTest n W d)
    (L : ℝ) (hL : 0≤L) (hA : ∀z,|A.base z|≤L)
    (z : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree) :
    |cavityGeneratedTaggedTestValue W A z| ≤ L*2^d := by
  unfold cavityGeneratedTaggedTestValue
  rw [abs_mul,Finset.abs_prod]
  have hp : (∏i : Fin d,|cavityGeneratedForestPairDefect n W (A.pairs i) z.1 z.2|) ≤
      ∏i : Fin d,(2:ℝ) :=
    Finset.prod_le_prod₀ (fun i _=>abs_nonneg _) (fun i _=>
      cavityGeneratedForestPairDefect_abs_le_two W (A.pairs i) z.1 z.2)
  simpa using mul_le_mul (hA z) hp (Finset.prod_nonneg fun i _=>abs_nonneg _) hL

end QuantitativeFollowup
