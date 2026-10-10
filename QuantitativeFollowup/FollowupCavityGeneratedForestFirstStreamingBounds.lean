module
public import QuantitativeFollowup.FollowupCavityGeneratedForestStreamingReplacementBasis
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingSourceResponseBounds

@[expose] public section

/-! A count-only bound for the genuine whole-forest first response.
Other component probabilities are frozen at the differentiation point,
and their actual average partial test keeps the original uniform bound.
Derivative uniqueness compares true curves without dividing by alpha. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n : ℕ} {I : Type*} [Fintype I]
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private theorem old_terminal_weighted_singletons {A : Type*} [Fintype A]
    {j : ℕ} (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy j)
    (coeff : A → ℝ) (label : A → TerminalSpins (Configuration (n+1)) T) :
    nativeStreamingOldTerminalExpectation D μ a q T
      (fun τ => ∑η, coeff η * cavityGeneratedTerminalSingletonTest (label η) τ) =
      ∑η, coeff η * nativeStreamingOldTerminalExpectation D μ a q T
        (cavityGeneratedTerminalSingletonTest (label η)) := by
  classical
  have hi (η : A) : Integrable (fun z => coeff η *
      cavityGeneratedTerminalSingletonTest (label η) (finiteCascadeRecordTerminalSpins T z.2))
      (anisotropicRecordedProfileTreeLaw D μ a q T) := by
    apply (integrable_const (c := |coeff η|)).mono'
      (((measurable_of_finite (cavityGeneratedTerminalSingletonTest (label η))).comp
        ((measurable_finiteCascadeRecordTerminalSpins T).comp measurable_snd)).const_mul
          (coeff η)).aestronglyMeasurable
    exact .of_forall fun z => by
      rw [Real.norm_eq_abs]
      by_cases h : finiteCascadeRecordTerminalSpins T z.2=label η
      · simp [cavityGeneratedTerminalSingletonTest,h]
      · simp [cavityGeneratedTerminalSingletonTest,h,abs_nonneg]
  unfold nativeStreamingOldTerminalExpectation
  rw [integral_finsetSum _ (fun η _ => hi η)]
  simp_rw [integral_const_mul]

private theorem averaged_partial_curve_basis
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (J : I → ℕ)
    (T : (i : I) → FiniteTerminalGenealogy (J i)) (q : I → ℕ → Paper.Overlap)
    (F : CavityGeneratedForestTerminalSample (n := n) J T → ℝ) (c : I)
    (u v : ℝ) (hu : u∈Icc (0:ℝ) 1) (hv : v∈Icc (0:ℝ) 1) :
    followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a (q c) (T c)
      (cavityGeneratedForestAveragedPartialTerminalTest
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a J T q F c) v =
      ∑σ : CavityGeneratedForestTerminalSample (n := n) J T,
        (F σ * ∏d∈Finset.univ.erase c,
          nativeStreamingOldTerminalExpectation (followupCavitySpinModel n β ρ hβ hρ u hu)
            μ a (q d) (T d) (cavityGeneratedTerminalSingletonTest (σ d))) *
        followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a (q c) (T c)
          (cavityGeneratedTerminalSingletonTest (σ c)) v := by
  classical
  let D := followupCavitySpinModel n β ρ hβ hρ u hu
  let coeff (σ : CavityGeneratedForestTerminalSample (n := n) J T) :=
    F σ * ∏d∈Finset.univ.erase c,nativeStreamingOldTerminalExpectation D μ a
      (q d) (T d) (cavityGeneratedTerminalSingletonTest (σ d))
  have hG : cavityGeneratedForestAveragedPartialTerminalTest D μ a J T q F c =
      fun τ => ∑σ : CavityGeneratedForestTerminalSample (n := n) J T,
        coeff σ * cavityGeneratedTerminalSingletonTest (σ c) τ := by
    funext τ
    rw [cavityGeneratedForestAveragedPartialTerminalTest_eq_basis]
    apply Finset.sum_congr rfl
    intro σ _
    dsimp [coeff]
    ring
  rw [hG,followupCavityNativeTerminalExpectation_eq_old_terminal β ρ hβ hρ μ a _ _ _ v hv,
    old_terminal_weighted_singletons]
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  exact (followupCavityNativeTerminalExpectation_eq_old_terminal β ρ hβ hρ μ a
    (q c) (T c) (cavityGeneratedTerminalSingletonTest (σ c)) v hv).symm

theorem cavityGeneratedForestFirstStreaming_scaled_eq_averaged_partial
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a) (J : I → ℕ)
    (T : (i : I) → FiniteTerminalGenealogy (J i)) (q : I → ℕ → Paper.Overlap)
    (hq : ∀i,Antitone (q i)) (hJ : ∀i,0<J i)
    (hzero : ∀i,(q i 0:ℝ)=1) (htop : ∀i,(q i (J i):ℝ)=0)
    (F : CavityGeneratedForestTerminalSample (n := n) J T → ℝ)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    (followupCavityAlpha n β ρ/2)*cavityGeneratedForestFirstStreamingBracket
      β ρ hβ hρ μ a J T q F u hu =
      ∑c : I, (followupCavityAlpha n β ρ/2)*nativeStreamingSourceSixBracket
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a (q c) (T c)
        (cavityGeneratedForestAveragedPartialTerminalTest
          (followupCavitySpinModel n β ρ hβ hρ u hu) μ a J T q F c) := by
  classical
  let κ := followupCavityAlpha n β ρ/2
  let D := followupCavitySpinModel n β ρ hβ hρ u hu
  let coeff (c : I) (σ : CavityGeneratedForestTerminalSample (n := n) J T) :=
    F σ * ∏d∈Finset.univ.erase c,nativeStreamingOldTerminalExpectation D μ a
      (q d) (T d) (cavityGeneratedTerminalSingletonTest (σ d))
  have hc (c : I) : κ*nativeStreamingSourceSixBracket D μ a (q c) (T c)
      (cavityGeneratedForestAveragedPartialTerminalTest D μ a J T q F c) =
      ∑σ : CavityGeneratedForestTerminalSample (n := n) J T,
        coeff c σ * (κ*nativeStreamingSourceSixBracket D μ a (q c) (T c)
          (cavityGeneratedTerminalSingletonTest (σ c))) := by
    have hd := hasDerivWithinAt_nativeStreamingSource_actual hn β ρ hβ hρ μ a ha hfloor
      (q c) (hq c) (hJ c) (hzero c) (htop c) (T c)
      (cavityGeneratedForestAveragedPartialTerminalTest D μ a J T q F c) u hu
    have hs : HasDerivWithinAt
        (fun v => ∑σ : CavityGeneratedForestTerminalSample (n := n) J T,
          coeff c σ * followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a (q c) (T c)
            (cavityGeneratedTerminalSingletonTest (σ c)) v)
        (∑σ : CavityGeneratedForestTerminalSample (n := n) J T,
          coeff c σ * (κ*nativeStreamingSourceSixBracket D μ a (q c) (T c)
            (cavityGeneratedTerminalSingletonTest (σ c)))) (Icc (0:ℝ) 1) u := by
      simpa only [Finset.sum_apply] using
        HasDerivWithinAt.fun_sum (u := Finset.univ) (fun σ _ =>
          (hasDerivWithinAt_nativeStreamingSource_actual hn β ρ hβ hρ μ a ha hfloor
            (q c) (hq c) (hJ c) (hzero c) (htop c) (T c)
            (cavityGeneratedTerminalSingletonTest (σ c)) u hu).const_mul (coeff c σ))
    have hs' := hs.congr_of_mem (fun v hv =>
      averaged_partial_curve_basis β ρ hβ hρ μ a J T q F c u v hu hv) hu
    exact (hd.derivWithin (uniqueDiffOn_Icc (by norm_num : (0:ℝ)<1) u hu)).symm.trans
      (hs'.derivWithin (uniqueDiffOn_Icc (by norm_num : (0:ℝ)<1) u hu))
  change κ*cavityGeneratedForestFirstStreamingBracket β ρ hβ hρ μ a J T q F u hu =
    ∑c : I,κ*nativeStreamingSourceSixBracket D μ a (q c) (T c)
      (cavityGeneratedForestAveragedPartialTerminalTest D μ a J T q F c)
  simp_rw [hc]
  unfold cavityGeneratedForestFirstStreamingBracket
  have hp (σ : CavityGeneratedForestTerminalSample (n := n) J T) (d : I) :
      followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a (q d) (T d)
        (cavityGeneratedTerminalSingletonTest (σ d)) u =
        nativeStreamingOldTerminalExpectation D μ a (q d) (T d)
          (cavityGeneratedTerminalSingletonTest (σ d)) :=
    followupCavityNativeTerminalExpectation_eq_old_terminal β ρ hβ hρ μ a
      (q d) (T d) (cavityGeneratedTerminalSingletonTest (σ d)) u hu
  simp_rw [hp,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro σ _
  dsimp [coeff,κ,D]
  ring

theorem abs_cavityGeneratedForestFirstStreaming_scaled_le
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a) (J : I → ℕ)
    (T : (i : I) → FiniteTerminalGenealogy (J i)) (q : I → ℕ → Paper.Overlap)
    (hq : ∀i,Antitone (q i)) (hJ : ∀i,0<J i)
    (hzero : ∀i,(q i 0:ℝ)=1) (htop : ∀i,(q i (J i):ℝ)=0)
    (F : CavityGeneratedForestTerminalSample (n := n) J T → ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀σ,|F σ|≤C)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    |(followupCavityAlpha n β ρ/2)*cavityGeneratedForestFirstStreamingBracket
      β ρ hβ hρ μ a J T q F u hu| ≤
      ∑c : I,7*β^2*(FiniteCascadeGenealogy.leafCount (asGenealogy (T c)):ℝ)^2*C := by
  classical
  rw [cavityGeneratedForestFirstStreaming_scaled_eq_averaged_partial
    hn β ρ hβ hρ μ a ha hfloor J T q hq hJ hzero htop F u hu]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro c _
  exact abs_nativeStreamingSource_response_le hn β ρ hβ hρ μ a ha hfloor
    (q c) (hq c) (hJ c) (hzero c) (htop c) (T c)
    (cavityGeneratedForestAveragedPartialTerminalTest
      (followupCavitySpinModel n β ρ hβ hρ u hu) μ a J T q F c)
    _ le_rfl C hC (fun τ => abs_cavityGeneratedForestAveragedPartialTerminalTest_le
      _ μ a J T q F C hF c τ) u hu

end QuantitativeFollowup
