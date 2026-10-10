module
public import QuantitativeFollowup.FollowupCavityGeneratedStreamingThreeDefects

@[expose] public section

/-! Physical pair tags in the actual constructed forest. Each pair stays
inside its selected component; different tags may use independent components.
Tagged tests retain an arbitrary joint base observable and all actual defects. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
variable {m n d : ℕ}

structure CavityGeneratedForestPair (W : CavityGeneratedConstructedForest m) where
  component : Fin W.componentCount
  first : ObservationLeaf (W.tree component)
  second : ObservationLeaf (W.tree component)

def cavityGeneratedForestPairDefect (n : ℕ) (W : CavityGeneratedConstructedForest m)
    (t : CavityGeneratedForestPair W) (h : CavityGeneratedHistory Paper.Overlap m)
    (σ : CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree) : ℝ :=
  cavitySpinOverlapDefect n
    (W.clockTemplate.clock h t.component (observationCommonLevel (W.tree t.component) t.first t.second))
    (observationTerminalSpin (W.tree t.component) t.first (σ t.component))
    (observationTerminalSpin (W.tree t.component) t.second (σ t.component))

structure CavityGeneratedTaggedTest (n : ℕ) (W : CavityGeneratedConstructedForest m) (d : ℕ) where
  base : CavityGeneratedHistory Paper.Overlap m ×
    CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ
  pairs : Fin d → CavityGeneratedForestPair W

def cavityGeneratedTaggedTestValue (W : CavityGeneratedConstructedForest m)
    (A : CavityGeneratedTaggedTest n W d)
    (z : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree) : ℝ :=
  A.base z * ∏i : Fin d,cavityGeneratedForestPairDefect n W (A.pairs i) z.1 z.2

end QuantitativeFollowup
