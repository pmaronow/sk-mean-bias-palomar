module
public import QuantitativeFollowup.FollowupCavityGeneratedForestFirstStreamingBounds
public import QuantitativeFollowup.FollowupCavityGeneratedRawForestHistoryStreamingKernel
public import FourPapersCommon.WithinIntegralDerivative
public import FourPapersCommon.WithinDerivativeMeasurable
public import Mathlib.Probability.Kernel.MeasurableIntegral

@[expose] public section

/-! Genuine streaming under an arbitrary finite retained-history integral.
The actual observed trees may have any measurable unary clock slices. The value
slice is measurable through the actual whole-forest terminal kernel;
the derivative slice is measurable through actual inward secants. A
count-only common bound justifies differentiation on the closed interval.
The original joint history and terminal test remains in every response. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n C : ℕ} {X : Type*} [MeasurableSpace X]
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def followupCavityGeneratedRawForestHistoryExpectation
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (J : Fin C → ℕ) (T : (c : Fin C) → FiniteTerminalGenealogy (J c))
    (q : X → Fin C → ℕ → Paper.Overlap)
    (M : Measure X)
    (F : X →
      CavityGeneratedForestTerminalSample (n := n) J T → ℝ) (u : ℝ) : ℝ :=
  ∫h,followupCavityGeneratedForestTerminalExpectation β ρ hβ hρ μ a
    J T (q h) (F h) u ∂M

def followupCavityGeneratedRawForestHistoryFirstResponse
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (J : Fin C → ℕ) (T : (c : Fin C) → FiniteTerminalGenealogy (J c))
    (q : X → Fin C → ℕ → Paper.Overlap)
    (F : X →
      CavityGeneratedForestTerminalSample (n := n) J T → ℝ)
    (u : ℝ) (h : X) : ℝ :=
  if hu : u∈Icc (0:ℝ) 1 then
    (followupCavityAlpha n β ρ/2)*cavityGeneratedForestFirstStreamingBracket
      β ρ hβ hρ μ a J T (q h) (F h) u hu
  else 0

theorem stronglyMeasurable_followupCavityGeneratedRawForestHistory_value
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (J : Fin C → ℕ) (T : (c : Fin C) → FiniteTerminalGenealogy (J c))
    (q : X → Fin C → ℕ → Paper.Overlap)
    (F : X →
      CavityGeneratedForestTerminalSample (n := n) J T → ℝ)
    (hqm : ∀c j, Measurable (fun h => q h c j))
    (hq : ∀h c, Antitone (q h c))
    (hF : Measurable (Function.uncurry F)) (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    StronglyMeasurable (fun h => followupCavityGeneratedForestTerminalExpectation
      β ρ hβ hρ μ a J T (q h) (F h) u) := by
  have H := hF.stronglyMeasurable.integral_kernel_prod_right'
    (κ := cavityGeneratedRawForestTerminalKernel (followupCavitySpinModel n β ρ hβ hρ u hu) μ a J T q hqm hq)
  simpa only [followupCavityGeneratedForestTerminalExpectation,dif_pos hu,
    Function.uncurry_apply_pair,cavityGeneratedRawForestTerminalKernel_apply] using H

theorem followupCavityGeneratedRawForestHistory_streaming_data
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a) (J : Fin C → ℕ) (T : (c : Fin C) → FiniteTerminalGenealogy (J c))
    (q : X → Fin C → ℕ → Paper.Overlap)
    (M : Measure X) [IsFiniteMeasure M]
    (F : X →
      CavityGeneratedForestTerminalSample (n := n) J T → ℝ)
    (hqm : ∀c j, Measurable (fun h => q h c j))
    (hq : ∀h c, Antitone (q h c)) (hJ : ∀c, 0<J c)
    (hzero : ∀h c, (q h c 0 : ℝ)=1)
    (htop : ∀h c, (q h c (J c) : ℝ)=0)
    (hF : Measurable (Function.uncurry F)) (L : ℝ) (hL : 0≤L)
    (hbound : ∀h σ,|F h σ|≤L) (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    Integrable (followupCavityGeneratedRawForestHistoryFirstResponse β ρ hβ hρ μ a J T q F u) M ∧
    HasDerivWithinAt (followupCavityGeneratedRawForestHistoryExpectation β ρ hβ hρ μ a J T q M F)
      (∫h,followupCavityGeneratedRawForestHistoryFirstResponse β ρ hβ hρ μ a J T q F u h ∂M)
      (Icc (0:ℝ) 1) u := by
  let H := fun v h => followupCavityGeneratedForestTerminalExpectation β ρ hβ hρ μ a
    J T (q h) (F h) v
  let G := followupCavityGeneratedRawForestHistoryFirstResponse β ρ hβ hρ μ a J T q F
  let B : ℝ := ∑c : Fin C,
    7*β^2*(FiniteCascadeGenealogy.leafCount (asGenealogy (T c)):ℝ)^2*L
  have hHm (v : ℝ) (hv : v∈Icc (0:ℝ) 1) : AEStronglyMeasurable (H v) M :=
    (stronglyMeasurable_followupCavityGeneratedRawForestHistory_value β ρ hβ hρ μ a J T q F hqm hq hF v hv).aestronglyMeasurable
  have hd : ∀ᵐh∂M,∀v∈Icc (0:ℝ) 1,
      HasDerivWithinAt (fun t => H t h) (G v h) (Icc (0:ℝ) 1) v :=
    .of_forall fun h v hv => by
      simpa only [H,G,followupCavityGeneratedRawForestHistoryFirstResponse,dif_pos hv] using
        hasDerivWithinAt_followupCavityGeneratedForestTerminalExpectation hn β ρ hβ hρ
          μ a ha hfloor J T (q h)
          (hq h) hJ (hzero h) (htop h) (F h) v hv
  have hGm (v : ℝ) (hv : v∈Icc (0:ℝ) 1) : AEStronglyMeasurable (G v) M :=
    aestronglyMeasurable_of_ae_hasDerivWithinAt_Icc01 H (G v) v hv hHm
      (hd.mono fun h hh => hh v hv)
  have hi : Integrable (H u) M := (integrable_const L).mono' (hHm u hu)
    (.of_forall fun h => by
      simpa only [H,followupCavityGeneratedForestTerminalExpectation,dif_pos hu,
        probReal_univ,mul_one] using
        norm_integral_le_of_norm_le_const
          (μ := (cavityGeneratedNativeForestTerminalProbability
            (followupCavitySpinModel n β ρ hβ hρ u hu) μ a J T
              (q h) : Measure _))
          (f := F h) (C := L) (.of_forall fun σ => by
            simpa only [Real.norm_eq_abs] using hbound h σ))
  have hb : ∀ᵐh∂M,∀v∈Icc (0:ℝ) 1,‖G v h‖≤B :=
    .of_forall fun h v hv => by
      simpa only [G,followupCavityGeneratedRawForestHistoryFirstResponse,dif_pos hv,
        Real.norm_eq_abs,B] using
        abs_cavityGeneratedForestFirstStreaming_scaled_le hn β ρ hβ hρ μ a ha hfloor
          J T (q h) (hq h) hJ (hzero h) (htop h) (F h) L hL (hbound h) v hv
  refine ⟨(integrable_const B).mono' (hGm u hu) (hb.mono fun h hh => hh u hu), ?_⟩
  exact hasDerivWithinAt_integral_of_uniform_derivative H G (fun _ => B)
    (Icc (0:ℝ) 1) (convex_Icc 0 1) u hu hHm hi hGm (integrable_const B) hb hd

end QuantitativeFollowup
