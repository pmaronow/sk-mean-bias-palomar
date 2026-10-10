module
public import QuantitativeFollowup.FollowupCavityDominatedSixCubic
public import QuantitativeFollowup.FollowupCavitySixTermEndpoints
public import QuantitativeFollowup.FollowupCavityCubicComparison

@[expose] public section

/-! Actual finite cavity endpoint increments are bounded by the
two-defect cubic budget at any chosen interpolation endpoint. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem finiteCascadeUnweightedBranchSum_scale_le (χ η : ℕ → ℝ) (E : ℝ)
    (h : ∀d, χ d ≤ E*η d) {j : ℕ} (T : FiniteTerminalGenealogy j) :
    finiteCascadeUnweightedBranchSum χ T ≤ E*finiteCascadeUnweightedBranchSum η T := by
  induction T with
  | leaf => simp only [finiteCascadeUnweightedBranchSum,mul_zero,le_refl]
  | advance T ih => exact ih
  | @fork j T U ihT ihU =>
    simp only [finiteCascadeUnweightedBranchSum,mul_add]
    exact add_le_add (add_le_add ihT ihU) (h j)

theorem followupCavityPhysicalExpectation_dominatedPair_sub_le
    (hn : 0 < n) (β ρ : ℝ) (hβ : 0 < β) (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2)) (i l : Fin 2 → ObservationLeaf (trimRoot T))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy T) → ℝ)
    (hdom : ∀r, |followupCavityPhysicalRecordObservable n T F r| ≤
      |cavityRecordedPairProduct s (trimRoot T) i l r|)
    (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1)
    (x y : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    let D := followupCavitySpinModel n β ρ hβ hρ v hv
    |followupCavityPhysicalExpectation n β ρ hβ hρ s a T F y-
      followupCavityPhysicalExpectation n β ρ hβ hρ s a T F x| ≤
      (followupCavityAlpha n β ρ/2*(15*(FiniteCascadeGenealogy.leafCount (asGenealogy T) : ℝ)^2)*
        Real.exp (21*β^2)*(cavityThirdMoment D (Paper.parisiSchemeMeasure s) a+
          finiteCascadeUnweightedBranchSum (fun d => cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a
            (cavityProfileLevel s d)) (trimRoot T)))*|y-x| := by
  dsimp only
  let f := followupCavityPhysicalExpectation n β ρ hβ hρ s a T F
  let Q := followupCavitySixTermResponse n β ρ hβ hρ s a T F
  let L : ℝ := FiniteCascadeGenealogy.leafCount (asGenealogy T)
  let E := Real.exp (21*β^2)
  let D := followupCavitySpinModel n β ρ hβ hρ v hv
  let M := cavityThirdMoment D (Paper.parisiSchemeMeasure s) a
  let B := finiteCascadeUnweightedBranchSum
    (fun d => cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot T)
  let K := followupCavityAlpha n β ρ/2*(15*L^2)*E*(M+B)
  have hf (z) (hz : z ∈ Icc (0 : ℝ) 1) : HasDerivWithinAt f (Q z) (Icc (0 : ℝ) 1) z := by
    simpa only [f,Q,followupCavitySixTermResponse,dite_eq_left hz] using
      hasDerivWithinAt_followupCavityPhysicalExpectation_six_terms_closed hn β ρ hβ hρ s a ha has hq T F z hz
  have hfloor : a ≤ Paper.parisiCDF (Paper.parisiSchemeMeasure s) 0 := by
    have hh := parisiSchemeMeasure_mem_scalarFloor s a ha.1 has hq
    rw [mem_scalarFloor_iff,zeroMass_eq_parisiCDF_zero] at hh
    exact hh
  have hQ (z) (hz : z ∈ Icc (0 : ℝ) 1) : ‖Q z‖ ≤ K := by
    have hα := followupCavityAlpha_nonneg n β ρ hρ.2
    have hb := cavityMarkedSix_dominatedPair_cubic_le hn
      (followupCavitySpinModel n β ρ hβ hρ z hz) s a ha has hq T i l
      (followupCavityPhysicalRecordObservable n T F) (measurable_followupCavityPhysicalRecordObservable T F) hdom
    have hM := cavityThirdMoment_comparison hn β ρ hβ hρ (Paper.parisiSchemeMeasure s) a ha hfloor z v hz hv
    have hB := finiteCascadeUnweightedBranchSum_scale_le
      (fun d => cavityCubicPairMoment (followupCavitySpinModel n β ρ hβ hρ z hz)
        (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d))
      (fun d => cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) E
      (fun d => cavityCubicPairMoment_comparison hn β ρ hβ hρ (Paper.parisiSchemeMeasure s) a ha hfloor
        (cavityProfileLevel s d) z v hz hv) (trimRoot T)
    dsimp only [Q]
    rw [followupCavitySixTermResponse,dite_eq_left hz,Real.norm_eq_abs,abs_mul,
      abs_of_nonneg (by positivity : 0 ≤ followupCavityAlpha n β ρ/2)]
    apply (mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ followupCavityAlpha n β ρ/2)).trans
    have hs := add_le_add hM hB
    have hh := mul_le_mul_of_nonneg_left hs
      (show 0 ≤ followupCavityAlpha n β ρ/2*(15*L^2) by positivity)
    change _ ≤ K
    dsimp only [K,M,B,E,L,D] at hh ⊢
    nlinarith only [hh]
  have hh := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le hf hQ hx hy
  simpa only [Real.norm_eq_abs,f,K,L,E,M,B,D] using hh

end QuantitativeFollowup
