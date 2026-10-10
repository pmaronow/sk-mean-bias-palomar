module
public import QuantitativeFollowup.FollowupCavityGeneratedForestFirstStreamingBasis
public import Mathlib.Analysis.Calculus.Deriv.Mul

@[expose] public section

/-! Genuine first streaming for an arbitrary joint terminal test on the
whole independent forest. The configuration basis is differentiated by
the actual component streaming formula and finite Leibniz; the original
joint coefficient is retained in every summand. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n : ℕ} {I : Type*} [Fintype I]
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def cavityGeneratedForestFirstStreamingBracket
    (β ρ : ℝ) (hβ : 0 < β) (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (J : I → ℕ)
    (T : (i : I) → FiniteTerminalGenealogy (J i)) (q : I → ℕ → Paper.Overlap)
    (F : CavityGeneratedForestTerminalSample (n := n) J T → ℝ)
    (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : ℝ := by
  classical
  exact ∑ σ : CavityGeneratedForestTerminalSample (n := n) J T,
    F σ * ∑ c : I,
      nativeStreamingSourceSixBracket (followupCavitySpinModel n β ρ hβ hρ u hu)
        μ a (q c) (T c) (cavityGeneratedTerminalSingletonTest (σ c)) *
      ∏ d ∈ Finset.univ.erase c,
        followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a (q d) (T d)
          (cavityGeneratedTerminalSingletonTest (σ d)) u

theorem hasDerivWithinAt_followupCavityGeneratedForestTerminalExpectation
    (hn : 0 < n) (β ρ : ℝ) (hβ : 0 < β) (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hfloor : μ ∈ scalarFloor a) (J : I → ℕ)
    (T : (i : I) → FiniteTerminalGenealogy (J i)) (q : I → ℕ → Paper.Overlap)
    (hq : ∀ i, Antitone (q i)) (hJ : ∀ i, 0 < J i)
    (hzero : ∀ i, (q i 0 : ℝ) = 1) (htop : ∀ i, (q i (J i) : ℝ) = 0)
    (F : CavityGeneratedForestTerminalSample (n := n) J T → ℝ)
    (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt (followupCavityGeneratedForestTerminalExpectation β ρ hβ hρ μ a J T q F)
      ((followupCavityAlpha n β ρ / 2) *
        cavityGeneratedForestFirstStreamingBracket β ρ hβ hρ μ a J T q F u hu)
      (Icc (0 : ℝ) 1) u := by
  classical
  let κ := followupCavityAlpha n β ρ / 2
  let D := followupCavitySpinModel n β ρ hβ hρ u hu
  let p (σ : CavityGeneratedForestTerminalSample (n := n) J T) (i : I) :=
    followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a (q i) (T i)
      (cavityGeneratedTerminalSingletonTest (σ i))
  let B (σ : CavityGeneratedForestTerminalSample (n := n) J T) (i : I) :=
    nativeStreamingSourceSixBracket D μ a (q i) (T i)
      (cavityGeneratedTerminalSingletonTest (σ i))
  have hd (σ : CavityGeneratedForestTerminalSample (n := n) J T) (i : I) :
      HasDerivWithinAt (p σ i) (κ * B σ i) (Icc (0 : ℝ) 1) u :=
    hasDerivWithinAt_nativeStreamingSource_actual hn β ρ hβ hρ μ a ha hfloor
      (q i) (hq i) (hJ i) (hzero i) (htop i) (T i)
      (cavityGeneratedTerminalSingletonTest (σ i)) u hu
  have hprod (σ : CavityGeneratedForestTerminalSample (n := n) J T) :
      HasDerivWithinAt (fun v => ∏ i, p σ i v)
        (∑ i : I, (∏ j ∈ Finset.univ.erase i, p σ j u) * (κ * B σ i))
        (Icc (0 : ℝ) 1) u := by
    simpa only [smul_eq_mul] using
      HasDerivWithinAt.fun_finsetProd (u := Finset.univ) (fun i _ => hd σ i)
  have H : HasDerivWithinAt
      (fun v => ∑ σ : CavityGeneratedForestTerminalSample (n := n) J T, F σ * ∏ i, p σ i v)
      (∑ σ : CavityGeneratedForestTerminalSample (n := n) J T,
        F σ * ∑ i : I, (∏ j ∈ Finset.univ.erase i, p σ j u) * (κ * B σ i))
      (Icc (0 : ℝ) 1) u := by
    simpa only [Finset.sum_apply] using
      HasDerivWithinAt.fun_sum (u := Finset.univ) (fun σ _ => (hprod σ).const_mul (F σ))
  have hb (σ : CavityGeneratedForestTerminalSample (n := n) J T) :
      (∑ i : I, (∏ j ∈ Finset.univ.erase i, p σ j u) * (κ * B σ i)) =
        κ * ∑ i : I, B σ i * ∏ j ∈ Finset.univ.erase i, p σ j u := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have he :
      (∑ σ : CavityGeneratedForestTerminalSample (n := n) J T,
        F σ * ∑ i : I, (∏ j ∈ Finset.univ.erase i, p σ j u) * (κ * B σ i)) =
      (followupCavityAlpha n β ρ / 2) *
        cavityGeneratedForestFirstStreamingBracket β ρ hβ hρ μ a J T q F u hu := by
    change (∑ σ : CavityGeneratedForestTerminalSample (n := n) J T,
      F σ * ∑ i : I, (∏ j ∈ Finset.univ.erase i, p σ j u) * (κ * B σ i)) =
      κ * ∑ σ : CavityGeneratedForestTerminalSample (n := n) J T,
        F σ * ∑ i : I, B σ i * ∏ j ∈ Finset.univ.erase i, p σ j u
    simp_rw [hb]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    ring
  rw [he] at H
  apply H.congr_of_mem ?_ hu
  intro v hv
  exact followupCavityGeneratedForestTerminalExpectation_eq_basis β ρ hβ hρ μ a J T q F v hv

theorem continuousOn_followupCavityGeneratedForestTerminalExpectation
    (hn : 0 < n) (β ρ : ℝ) (hβ : 0 < β) (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hfloor : μ ∈ scalarFloor a) (J : I → ℕ)
    (T : (i : I) → FiniteTerminalGenealogy (J i)) (q : I → ℕ → Paper.Overlap)
    (hq : ∀ i, Antitone (q i)) (hJ : ∀ i, 0 < J i)
    (hzero : ∀ i, (q i 0 : ℝ) = 1) (htop : ∀ i, (q i (J i) : ℝ) = 0)
    (F : CavityGeneratedForestTerminalSample (n := n) J T → ℝ) :
    ContinuousOn (followupCavityGeneratedForestTerminalExpectation β ρ hβ hρ μ a J T q F)
      (Icc (0 : ℝ) 1) :=
  fun u hu => (hasDerivWithinAt_followupCavityGeneratedForestTerminalExpectation hn β ρ hβ hρ
    μ a ha hfloor J T q hq hJ hzero htop F u hu).continuousWithinAt

end QuantitativeFollowup
