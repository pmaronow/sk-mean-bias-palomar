module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingActualSource
public import QuantitativeFollowup.FollowupCavityNativeStreamingBounds
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPatternNormalizerSourceDerivative
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPatternTerminalTestBounds

@[expose] public section

/-! Uniform response bounds come from the genuine native first jet.
They apply to every fixed terminal test and every admissible clock
schedule, including repeated clocks and both parameter endpoints. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
open FourPapersCommon.FiniteStreamingPolynomials
variable {n J : ℕ}
set_option maxHeartbeats 1100000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem abs_nativeStreamingSource_response_le
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (K : ℕ) (hK : FiniteCascadeGenealogy.leafCount (asGenealogy T)≤K)
    (C : ℝ) (hC : 0≤C) (hF : ∀σ,|F σ|≤C)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    |(followupCavityAlpha n β ρ/2)*nativeStreamingSourceSixBracket
      (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F|≤
      7*β^2*(K:ℝ)^2*C := by
  have hd := hasDerivWithinAt_nativeStreamingSource_actual hn β ρ hβ hρ μ a ha hfloor
    q hq hJ hzero htop T F u hu
  have he := hd.derivWithin (uniqueDiffOn_Icc (by norm_num : (0:ℝ)<1) u hu)
  have hb := abs_followupCavityNativeTerminalExpectation_withinJet_le hn β ρ hβ hρ
    μ a ha (scalarFloor_cdf_lower hfloor (by norm_num)) q hq hJ hzero htop T F C hC hF 1 u hu
  simp only [withinJet,growth,Nat.mul_zero,Nat.add_zero,mul_one] at hb
  rw [he] at hb
  apply hb.trans
  have hc : (FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)≤K := by exact_mod_cast hK
  gcongr


theorem abs_nativeStreamingOldTerminalExpectation_actual_le
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀σ,|F σ|≤C)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    |nativeStreamingOldTerminalExpectation
      (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F|≤C := by
  have hb := abs_followupCavityNativeTerminalExpectation_withinJet_le hn β ρ hβ hρ
    μ a ha (scalarFloor_cdf_lower hfloor (by norm_num)) q hq hJ hzero htop T F C hC hF 0 u hu
  simpa only [withinJet,growth,one_mul,
    followupCavityNativeTerminalExpectation_eq_old_terminal β ρ hβ hρ μ a q T F u hu] using hb

private theorem sourceBounds_binary_antitone (l : Paper.Overlap) :
    Antitone (anisotropicBinaryObservationSchedule l) := by
  apply antitone_nat_of_succ_le
  intro j
  cases j with
  | zero => exact l.property.2
  | succ j =>
    cases j with
    | zero => exact l.property.1
    | succ j => simp only [anisotropicBinaryObservationSchedule,le_refl]

theorem abs_nativeStreamingNormalizer_source_response_le
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀σ,|F σ|≤C)
    (l : Paper.Overlap) (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    let D := followupCavitySpinModel n β ρ hβ hρ u hu
    |(followupCavityAlpha n β ρ/2)*
        (nativeStreamingSourceSixBracket D μ a q T F *
          nativeStreamingOldTerminalExpectation D μ a (anisotropicBinaryObservationSchedule l)
            anisotropicBinaryObservationTree (nativeStreamingNormalizerBinaryTerminalTest n l) +
          nativeStreamingOldTerminalExpectation D μ a q T F *
            nativeStreamingSourceSixBracket D μ a (anisotropicBinaryObservationSchedule l)
              anisotropicBinaryObservationTree (nativeStreamingNormalizerBinaryTerminalTest n l))|≤
      7*β^2*((FiniteCascadeGenealogy.leafCount (asGenealogy T)+2:ℕ):ℝ)^2*(2*C) := by
  dsimp only
  let K := FiniteCascadeGenealogy.leafCount (asGenealogy T)
  let D := followupCavitySpinModel n β ρ hβ hρ u hu
  let Q := anisotropicBinaryObservationSchedule l
  let U := anisotropicBinaryObservationTree
  let G := nativeStreamingNormalizerBinaryTerminalTest n l
  have hQ := sourceBounds_binary_antitone l
  have hG := nativeStreamingNormalizerBinaryTerminalTest_abs_le n l
  have hR1 := abs_nativeStreamingSource_response_le hn β ρ hβ hρ μ a ha hfloor
    q hq hJ hzero htop T F K le_rfl C hC hF u hu
  have hR2 := abs_nativeStreamingSource_response_le hn β ρ hβ hρ μ a ha hfloor
    Q hQ (by norm_num) rfl rfl U G 2 (by norm_num [U,nativeStreamingNormalizerBinaryTree_leafCount])
    2 (by norm_num) hG u hu
  have hE1 := abs_nativeStreamingOldTerminalExpectation_actual_le hn β ρ hβ hρ μ a ha hfloor
    q hq hJ hzero htop T F C hC hF u hu
  have hE2 := abs_nativeStreamingOldTerminalExpectation_actual_le hn β ρ hβ hρ μ a ha hfloor
    Q hQ (by norm_num) rfl rfl U G 2 (by norm_num) hG u hu
  change |(followupCavityAlpha n β ρ/2)*
    (nativeStreamingSourceSixBracket D μ a q T F*nativeStreamingOldTerminalExpectation D μ a Q U G+
      nativeStreamingOldTerminalExpectation D μ a q T F*nativeStreamingSourceSixBracket D μ a Q U G)|≤_
  rw [show (followupCavityAlpha n β ρ/2)*
      (nativeStreamingSourceSixBracket D μ a q T F*nativeStreamingOldTerminalExpectation D μ a Q U G+
        nativeStreamingOldTerminalExpectation D μ a q T F*nativeStreamingSourceSixBracket D μ a Q U G)=
      ((followupCavityAlpha n β ρ/2)*nativeStreamingSourceSixBracket D μ a q T F)*
        nativeStreamingOldTerminalExpectation D μ a Q U G+
      nativeStreamingOldTerminalExpectation D μ a q T F*
        ((followupCavityAlpha n β ρ/2)*nativeStreamingSourceSixBracket D μ a Q U G) by ring]
  apply (abs_add_le _ _).trans
  rw [abs_mul (followupCavityAlpha n β ρ/2*nativeStreamingSourceSixBracket D μ a q T F)
    (nativeStreamingOldTerminalExpectation D μ a Q U G),
    abs_mul (nativeStreamingOldTerminalExpectation D μ a q T F)
      (followupCavityAlpha n β ρ/2*nativeStreamingSourceSixBracket D μ a Q U G)]
  have h1 := mul_le_mul hR1 hE2 (abs_nonneg _) (by positivity)
  have h2 := mul_le_mul hE1 hR2 (abs_nonneg _) hC
  apply (add_le_add h1 h2).trans
  simp only [Nat.cast_add,Nat.cast_ofNat]
  have hK0 : 0≤(K:ℝ) := Nat.cast_nonneg _
  have hp : 0≤β^2*C := mul_nonneg (sq_nonneg _) hC
  dsimp only [K] at hK0 ⊢
  nlinarith [mul_nonneg hp hK0]

end QuantitativeFollowup
