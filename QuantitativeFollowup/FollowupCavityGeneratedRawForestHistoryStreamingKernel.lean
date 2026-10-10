module
public import QuantitativeFollowup.FollowupCavityGeneratedForestJointLaw

@[expose] public section

/-! The genuine terminal kernel of an arbitrary observed forest with
measurable antitone clock slices. Unary observation levels may be any
measurable functions of the old history. No branch-label or law premise
is needed for this analytic supporting kernel. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n C : ℕ} {X : Type*} [MeasurableSpace X]

theorem measurable_cavityGeneratedRawForestTerminalMeasure
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (J : Fin C → ℕ) (T : (c : Fin C) → FiniteTerminalGenealogy (J c))
    (q : X → Fin C → ℕ → Paper.Overlap)
    (hqm : ∀c j,Measurable (fun h=>q h c j))
    (hq : ∀h c,Antitone (q h c)) :
    Measurable (fun h : X=>
      (cavityGeneratedNativeForestTerminalProbability D μ a J T (q h) :
        Measure (CavityGeneratedForestTerminalSample (n:=n) J T))) := by
  let Q : (Fin C → ℕ → Paper.Overlap) → Fin C → ℕ → Paper.Overlap :=
    fun z c=>cavityGeneratedClippedClock (z c)
  have hcts (c : Fin C) (j : ℕ) : Continuous (fun z : Fin C → ℕ → Paper.Overlap=>Q z c j) :=
    cavityGeneratedClippedClock_continuous (fun z : Fin C → ℕ → Paper.Overlap=>z c)
      (fun j=>(continuous_apply j).comp (continuous_apply c)) j
  have hc := continuous_cavityGeneratedNativeForestTerminalProbability_family
    D μ a J T Q (fun c j _=>hcts c j)
      (fun z c j _=>cavityGeneratedClippedClock_step_le (z c) j)
  have hm : Measurable q := measurable_pi_iff.mpr fun c=>
    measurable_pi_iff.mpr fun j=>hqm c j
  have heq (h : X) : Q (q h)=q h := by
    funext c j
    exact cavityGeneratedClippedClock_eq (q h c) j
      (fun i _=>hq h c (Nat.le_succ i)) j le_rfl
  apply Measure.measurable_of_measurable_coe
  intro E hE
  let F : CavityGeneratedForestTerminalSample (n:=n) J T → ℝ := E.indicator (fun _=>1)
  have hi : Continuous (fun z : Fin C → ℕ → Paper.Overlap=>
      ∫σ,F σ ∂(cavityGeneratedNativeForestTerminalProbability D μ a J T (Q z) : Measure _)) :=
    continuous_integral_probability_family (fun z=>F z.2)
      ((continuous_of_discreteTopology (f:=F)).comp continuous_snd) _ hc
  have he (z : Fin C → ℕ → Paper.Overlap) :
      ENNReal.ofReal (∫σ,F σ ∂(cavityGeneratedNativeForestTerminalProbability D μ a J T (Q z) : Measure _)) =
      (cavityGeneratedNativeForestTerminalProbability D μ a J T (Q z) : Measure _) E := by
    rw [show F=E.indicator (1 : CavityGeneratedForestTerminalSample (n:=n) J T→ℝ) from rfl,
      integral_indicator_one hE,ofReal_measureReal]
  have hmeasure : Measurable (fun z : Fin C → ℕ → Paper.Overlap=>
      (cavityGeneratedNativeForestTerminalProbability D μ a J T (Q z) : Measure _) E) :=
    (funext he) ▸ hi.measurable.ennreal_ofReal
  have H := hmeasure.comp hm
  simpa only [Function.comp_def,heq] using H

def cavityGeneratedRawForestTerminalKernel
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (J : Fin C → ℕ) (T : (c : Fin C) → FiniteTerminalGenealogy (J c))
    (q : X → Fin C → ℕ → Paper.Overlap)
    (hqm : ∀c j,Measurable (fun h=>q h c j))
    (hq : ∀h c,Antitone (q h c)) :
    Kernel X (CavityGeneratedForestTerminalSample (n:=n) J T) where
  toFun h := cavityGeneratedNativeForestTerminalProbability D μ a J T (q h)
  measurable' := measurable_cavityGeneratedRawForestTerminalMeasure D μ a J T q hqm hq

instance cavityGeneratedRawForestTerminalKernel_markov
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (J : Fin C → ℕ) (T : (c : Fin C) → FiniteTerminalGenealogy (J c))
    (q : X → Fin C → ℕ → Paper.Overlap)
    (hqm : ∀c j,Measurable (fun h=>q h c j))
    (hq : ∀h c,Antitone (q h c)) :
    IsMarkovKernel (cavityGeneratedRawForestTerminalKernel D μ a J T q hqm hq) where
  isProbabilityMeasure h := inferInstanceAs (IsProbabilityMeasure
    (cavityGeneratedNativeForestTerminalProbability D μ a J T (q h) :
      Measure (CavityGeneratedForestTerminalSample (n:=n) J T)))

theorem cavityGeneratedRawForestTerminalKernel_apply
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (J : Fin C → ℕ) (T : (c : Fin C) → FiniteTerminalGenealogy (J c))
    (q : X → Fin C → ℕ → Paper.Overlap)
    (hqm : ∀c j,Measurable (fun h=>q h c j))
    (hq : ∀h c,Antitone (q h c)) (h : X) :
    cavityGeneratedRawForestTerminalKernel D μ a J T q hqm hq h =
      (cavityGeneratedNativeForestTerminalProbability D μ a J T (q h) : Measure _) := rfl

end QuantitativeFollowup
