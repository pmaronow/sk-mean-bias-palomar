module
public import QuantitativeFollowup.FollowupCavityNativePairIncrement
public import QuantitativeFollowup.FollowupCavityFourObservationLaw

@[expose] public section

/-! Genuine integrated streaming of the four independent fresh siblings.
All three forks at their shared split are retained in the cubic budget. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def cavityFourRestPairProduct (n : ℕ) (p : Paper.Overlap)
    (σ : CavityFourTerminalSpins (n+1)) : ℝ :=
  (cavityRestOverlap n σ.1.1 σ.1.2-(p : ℝ))*(cavityRestOverlap n σ.2.1 σ.2.2-(p : ℝ))

def cavityFourPairFirst : Fin 2 → ObservationLeaf cavityFourObservationTree :=
  ![Sum.inl (Sum.inl ()),Sum.inr (Sum.inl ())]

def cavityFourPairSecond : Fin 2 → ObservationLeaf cavityFourObservationTree :=
  ![Sum.inl (Sum.inr ()),Sum.inr (Sum.inr ())]

theorem cavityFourRestPairProduct_domination (p : Paper.Overlap)
    (σ : TerminalSpins (Configuration (n+1)) cavityFourObservationTree) :
    |cavityFourRestPairProduct n p σ|≤
      |cavityObservationTerminalPairProduct (anisotropicBinaryObservationSchedule p)
        cavityFourObservationTree cavityFourPairFirst cavityFourPairSecond σ| := by
  change |(cavityRestOverlap n σ.1.1 σ.1.2-(p : ℝ))*(cavityRestOverlap n σ.2.1 σ.2.2-(p : ℝ))|≤
    |cavitySpinOverlapDefect n p σ.1.1 σ.1.2*cavitySpinOverlapDefect n p σ.2.1 σ.2.2|
  rw [abs_mul,abs_mul,cavitySpinOverlapDefect_abs_eq_rest,cavitySpinOverlapDefect_abs_eq_rest]

theorem finiteCascadeUnweightedBranchSum_four (χ : ℕ → ℝ) :
    finiteCascadeUnweightedBranchSum χ cavityFourObservationTree=3*χ 1 := by
  simp only [cavityFourObservationTree,finiteCascadeUnweightedBranchSum]
  ring

theorem followupCavityFourDescendant_sub_le_cubic
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (hfloor : a≤Paper.parisiCDF μ 0)
    (p : Paper.Overlap) (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1)
    (x y : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    let D := followupCavitySpinModel n β ρ hβ hρ v hv
    |(∫z,cavityFourRestPairProduct n p z.2
        ∂cavityFourDescendantLaw (followupCavitySpinModel n β ρ hβ hρ y hy) μ a p)-
      (∫z,cavityFourRestPairProduct n p z.2
        ∂cavityFourDescendantLaw (followupCavitySpinModel n β ρ hβ hρ x hx) μ a p)| ≤
      (followupCavityAlpha n β ρ/2*240*Real.exp (21*β^2)*
        (cavityThirdMoment D μ a+3*cavityCubicPairMoment D μ a p))*|y-x| := by
  dsimp only
  have hh := cavityNative_terminalPair_sub_le hn β ρ hβ hρ μ a ha hfloor
    (anisotropicBinaryObservationSchedule p) (anisotropicBinaryObservationSchedule_antitone p)
    2 (by norm_num) rfl rfl cavityFourObservationTree cavityFourPairFirst cavityFourPairSecond
    (cavityFourRestPairProduct n p) (cavityFourRestPairProduct_domination p) v hv x y hx hy
  dsimp only at hh
  rw [cavityFourObservation_energy_integral,cavityFourObservation_energy_integral,
    finiteCascadeUnweightedBranchSum_four] at hh
  convert hh using 1 <;> norm_num [cavityFourObservationTree,asGenealogy,FiniteCascadeGenealogy.leafCount,
    anisotropicBinaryObservationSchedule]

theorem followupCavityFourDescendant_sub_le
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (hfloor : a≤Paper.parisiCDF μ 0)
    (p : Paper.Overlap) (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1)
    (x y : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    let D := followupCavitySpinModel n β ρ hβ hρ v hv
    |(∫z,cavityFourRestPairProduct n p z.2
        ∂cavityFourDescendantLaw (followupCavitySpinModel n β ρ hβ hρ y hy) μ a p)-
      (∫z,cavityFourRestPairProduct n p z.2
        ∂cavityFourDescendantLaw (followupCavitySpinModel n β ρ hβ hρ x hx) μ a p)| ≤
      (360*β^2*Real.exp (21*β^2)*(cavityThirdMoment D μ a+cavityCubicPairMoment D μ a p))*|y-x| := by
  dsimp only
  apply (followupCavityFourDescendant_sub_le_cubic hn β ρ hβ hρ μ a ha hfloor p v hv x y hx hy).trans
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  have hM := cavityThirdMoment_nonneg (followupCavitySpinModel n β ρ hβ hρ v hv) μ a
  have hχ := (cavityCubicPairMoment_bounds (followupCavitySpinModel n β ρ hβ hρ v hv) μ a p).1
  have hα := followupCavityAlpha_nonneg n β ρ hρ.2
  have hαB : followupCavityAlpha n β ρ≤β^2 := by
    have hd := (followupCavityD_window n hn β ρ ⟨hρ.1.le,hρ.2⟩).2
    have hc : 0≤followupCavityC β ρ := mul_nonneg (sq_nonneg β) hρ.1.le
    unfold followupCavityD at hd
    linarith
  have h1 := mul_le_mul_of_nonneg_right hαB
    (mul_nonneg (Real.exp_nonneg (21*β^2)) (show 0≤cavityThirdMoment (followupCavitySpinModel n β ρ hβ hρ v hv) μ a+
      3*cavityCubicPairMoment (followupCavitySpinModel n β ρ hβ hρ v hv) μ a p by positivity))
  have h2 := mul_le_mul_of_nonneg_left (show
      cavityThirdMoment (followupCavitySpinModel n β ρ hβ hρ v hv) μ a+
        3*cavityCubicPairMoment (followupCavitySpinModel n β ρ hβ hρ v hv) μ a p≤
      3*(cavityThirdMoment (followupCavitySpinModel n β ρ hβ hρ v hv) μ a+
        cavityCubicPairMoment (followupCavitySpinModel n β ρ hβ hρ v hv) μ a p) by linarith)
    (mul_nonneg (sq_nonneg β) (Real.exp_nonneg (21*β^2)))
  nlinarith only [h1,h2]

end QuantitativeFollowup
