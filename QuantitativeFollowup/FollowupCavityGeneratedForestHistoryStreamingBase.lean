module
public import QuantitativeFollowup.FollowupCavityGeneratedForestFirstStreamingBounds
public import QuantitativeFollowup.FollowupCavityGeneratedForestJointLaw
public import FourPapersCommon.WithinIntegralDerivative
public import FourPapersCommon.WithinDerivativeMeasurable
public import Mathlib.Probability.Kernel.MeasurableIntegral

@[expose] public section

/-! Genuine streaming under a retained mark-history integral. The value
slice is measurable through the actual whole-forest terminal kernel;
the derivative slice is measurable through actual inward secants. A
count-only common bound justifies differentiation on the closed interval.
The original joint history and terminal test remains in every response. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n m : ℕ}
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def followupCavityGeneratedForestHistoryExpectation
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (W : CavityGeneratedConstructedForest m)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (F : CavityGeneratedHistory Paper.Overlap m →
      CavityGeneratedForestTerminalSample (n := n) W.depth W.tree → ℝ) (u : ℝ) : ℝ :=
  ∫h,followupCavityGeneratedForestTerminalExpectation β ρ hβ hρ μ a
    W.depth W.tree (W.clockTemplate.clock h) (F h) u ∂M

def followupCavityGeneratedForestHistoryFirstResponse
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (W : CavityGeneratedConstructedForest m)
    (F : CavityGeneratedHistory Paper.Overlap m →
      CavityGeneratedForestTerminalSample (n := n) W.depth W.tree → ℝ)
    (u : ℝ) (h : CavityGeneratedHistory Paper.Overlap m) : ℝ :=
  if hu : u∈Icc (0:ℝ) 1 then
    (followupCavityAlpha n β ρ/2)*cavityGeneratedForestFirstStreamingBracket
      β ρ hβ hρ μ a W.depth W.tree (W.clockTemplate.clock h) (F h) u hu
  else 0

private theorem constructed_clock_antitone (W : CavityGeneratedConstructedForest m)
    (h : CavityGeneratedHistory Paper.Overlap m) (c : Fin W.componentCount) :
    Antitone (W.clockTemplate.clock h c) :=
  antitone_nat_of_succ_le (W.clockTemplate.clock_step_le h c)

private theorem constructed_depth_pos (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) : 0<W.depth c := by
  by_contra h
  have hz : W.depth c=0 := by omega
  have hi := W.clockTemplate.clock_initial (fun _ => 0) c
  change W.clockTemplate.clock (fun _ => 0) c (W.depth c)=0 at hi
  rw [hz,W.clockTemplate.clock_terminal] at hi
  have hh := congrArg (fun x : Paper.Overlap => (x:ℝ)) hi
  norm_num at hh

theorem stronglyMeasurable_followupCavityGeneratedForestHistory_value
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (W : CavityGeneratedConstructedForest m)
    (F : CavityGeneratedHistory Paper.Overlap m →
      CavityGeneratedForestTerminalSample (n := n) W.depth W.tree → ℝ)
    (hF : Measurable (Function.uncurry F)) (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    StronglyMeasurable (fun h => followupCavityGeneratedForestTerminalExpectation
      β ρ hβ hρ μ a W.depth W.tree (W.clockTemplate.clock h) (F h) u) := by
  have H := hF.stronglyMeasurable.integral_kernel_prod_right'
    (κ := cavityGeneratedForestTerminalKernel (followupCavitySpinModel n β ρ hβ hρ u hu) μ a W)
  simpa only [followupCavityGeneratedForestTerminalExpectation,dif_pos hu,
    Function.uncurry_apply_pair,cavityGeneratedForestTerminalKernel_apply] using H

theorem hasDerivWithinAt_followupCavityGeneratedForestHistoryExpectation
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a) (W : CavityGeneratedConstructedForest m)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [IsFiniteMeasure M]
    (F : CavityGeneratedHistory Paper.Overlap m →
      CavityGeneratedForestTerminalSample (n := n) W.depth W.tree → ℝ)
    (hF : Measurable (Function.uncurry F)) (C : ℝ) (hC : 0≤C)
    (hbound : ∀h σ,|F h σ|≤C) (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (followupCavityGeneratedForestHistoryExpectation β ρ hβ hρ μ a W M F)
      (∫h,followupCavityGeneratedForestHistoryFirstResponse β ρ hβ hρ μ a W F u h ∂M)
      (Icc (0:ℝ) 1) u := by
  let H := fun v h => followupCavityGeneratedForestTerminalExpectation β ρ hβ hρ μ a
    W.depth W.tree (W.clockTemplate.clock h) (F h) v
  let G := followupCavityGeneratedForestHistoryFirstResponse β ρ hβ hρ μ a W F
  let B : ℝ := ∑c : Fin W.componentCount,
    7*β^2*(FiniteCascadeGenealogy.leafCount (asGenealogy (W.tree c)):ℝ)^2*C
  have hHm (v : ℝ) (hv : v∈Icc (0:ℝ) 1) : AEStronglyMeasurable (H v) M :=
    (stronglyMeasurable_followupCavityGeneratedForestHistory_value β ρ hβ hρ μ a W F hF v hv).aestronglyMeasurable
  have hd : ∀ᵐh∂M,∀v∈Icc (0:ℝ) 1,
      HasDerivWithinAt (fun t => H t h) (G v h) (Icc (0:ℝ) 1) v :=
    .of_forall fun h v hv => by
      simpa only [H,G,followupCavityGeneratedForestHistoryFirstResponse,dif_pos hv] using
        hasDerivWithinAt_followupCavityGeneratedForestTerminalExpectation hn β ρ hβ hρ
          μ a ha hfloor W.depth W.tree (W.clockTemplate.clock h)
          (constructed_clock_antitone W h) (constructed_depth_pos W)
          (fun c => congrArg (fun x : Paper.Overlap => (x:ℝ)) (W.clockTemplate.clock_terminal h c))
          (fun c => congrArg (fun x : Paper.Overlap => (x:ℝ)) (W.clockTemplate.clock_initial h c)) (F h) v hv
  have hGm (v : ℝ) (hv : v∈Icc (0:ℝ) 1) : AEStronglyMeasurable (G v) M :=
    aestronglyMeasurable_of_ae_hasDerivWithinAt_Icc01 H (G v) v hv hHm
      (hd.mono fun h hh => hh v hv)
  have hi : Integrable (H u) M := (integrable_const C).mono' (hHm u hu)
    (.of_forall fun h => by
      simpa only [H,followupCavityGeneratedForestTerminalExpectation,dif_pos hu,
        probReal_univ,mul_one] using
        norm_integral_le_of_norm_le_const
          (μ := (cavityGeneratedNativeForestTerminalProbability
            (followupCavitySpinModel n β ρ hβ hρ u hu) μ a W.depth W.tree
              (W.clockTemplate.clock h) : Measure _))
          (f := F h) (C := C) (.of_forall fun σ => by
            simpa only [Real.norm_eq_abs] using hbound h σ))
  have hb : ∀ᵐh∂M,∀v∈Icc (0:ℝ) 1,‖G v h‖≤B :=
    .of_forall fun h v hv => by
      simpa only [G,followupCavityGeneratedForestHistoryFirstResponse,dif_pos hv,
        Real.norm_eq_abs,B] using
        abs_cavityGeneratedForestFirstStreaming_scaled_le hn β ρ hβ hρ μ a ha hfloor
          W.depth W.tree (W.clockTemplate.clock h) (constructed_clock_antitone W h)
          (constructed_depth_pos W)
          (fun c => congrArg (fun x : Paper.Overlap => (x:ℝ)) (W.clockTemplate.clock_terminal h c))
          (fun c => congrArg (fun x : Paper.Overlap => (x:ℝ)) (W.clockTemplate.clock_initial h c)) (F h) C hC (hbound h) v hv
  exact hasDerivWithinAt_integral_of_uniform_derivative H G (fun _ => B)
    (Icc (0:ℝ) 1) (convex_Icc 0 1) u hu hHm hi hGm (integrable_const B) hb hd

end QuantitativeFollowup
