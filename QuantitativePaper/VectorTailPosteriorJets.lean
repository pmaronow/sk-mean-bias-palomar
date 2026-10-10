module
public import QuantitativePaper.VectorTailScoreBounds
public import QuantitativePaper.NormalizedExponentialJets

@[expose] public section

/-! Higher spatial jets of the actual finite posterior gradient. The bounds
depend on dimension alone, not on the number or sizes of profile cells. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ContDiff BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem vectorTailPosteriorLogDensity_lipschitz (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (j : ℕ) (hj : j ≤ k+2)
    (z : (Fin j → Field n) × Configuration n) :
    LipschitzWith (2*Real.sqrt (n : ℝ)).toNNReal
      (fun x => vectorTailPosteriorLogDensity s β t p x j z) := by
  have hs := (contDiff_vectorTailPosteriorLogDensity_initial_noise s β t p j z.2).comp
    (contDiff_id.prodMk (contDiff_const (c := z.1)))
  apply lipschitzWith_of_nnnorm_fderiv_le (hs.differentiable (by simp))
  intro x
  rw [←NNReal.coe_le_coe,coe_nnnorm,Real.coe_toNNReal _ (by positivity),
    ←norm_iteratedFDeriv_one]
  exact norm_vectorTailLogDensity_firstJet_le s β t p j hj x z

theorem aestronglyMeasurable_vectorTailPosterior_exponentialJet (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (j r : ℕ) (x : Field n) :
    AEStronglyMeasurable (fun z : (Fin j → Field n) × Configuration n =>
      iteratedFDeriv ℝ r
        (fun y => Real.exp (vectorTailPosteriorLogDensity s β t p y j z) • spinVector z.2) x)
      (vectorTailGaussianBase n j) := by
  letI : MeasurableSpace (Field n [×r]→L[ℝ] Field n) := borel _
  haveI : BorelSpace (Field n [×r]→L[ℝ] Field n) := ⟨rfl⟩
  let f := fun z : (Fin j → Field n) × Configuration n => iteratedFDeriv ℝ r
    (fun y => Real.exp (vectorTailPosteriorLogDensity s β t p y j z) • spinVector z.2) x
  have hc (σ : Configuration n) : Continuous (fun z : Fin j → Field n => f (z,σ)) := by
    let F := fun z : (Fin j → Field n) × Field n =>
      Real.exp (vectorTailPosteriorLogDensity s β t p z.2 j (z.1,σ)) • spinVector σ
    have hF : ContDiff ℝ ∞ F :=
      ((contDiff_vectorTailPosteriorLogDensity_initial_noise s β t p j σ).comp
        (contDiff_snd.prodMk contDiff_fst)).exp.smul_const _
    have hcF := continuous_fieldSlice_iteratedFDeriv F hF r
    have he : (fun z : Fin j → Field n => f (z,σ))=
        (fun z : (Fin j → Field n) × Field n => iteratedFDeriv ℝ r
          (fun y => F (z.1,y)) z.2) ∘ (fun z : Fin j → Field n => (z,x)) := rfl
    rw [he]
    exact hcF.comp (continuous_id.prodMk (continuous_const (y := x)))
  have hm : Measurable f := measurable_from_prod_countable_left fun σ => (hc σ).measurable
  have hs : TopologicalSpace.IsSeparable (⋃σ : Configuration n,range (fun z : Fin j → Field n => f (z,σ))) :=
    .iUnion fun σ => TopologicalSpace.isSeparable_range (hc σ)
  apply StronglyMeasurable.aestronglyMeasurable
  apply stronglyMeasurable_iff_measurable_separable.mpr
  refine ⟨hm,hs.mono ?_⟩
  rintro _ ⟨⟨z,σ⟩,rfl⟩
  exact mem_iUnion.mpr ⟨σ,mem_range.mpr ⟨z,rfl⟩⟩

theorem norm_vectorRecursion_jet_from_tailScore (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (N : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hB : ∀i,1 ≤ i → i ≤ N → ∀j,j ≤ k+2 → ∀x z,
      ‖iteratedFDeriv ℝ i (fun y => vectorTailPosteriorLogDensity s β t p y j z) x‖ ≤ K^i)
    (j : ℕ) (hj : j ≤ k+2) (r : ℕ) (hr : r ≤ N) (x : Field n) :
    ‖iteratedFDeriv ℝ (r+1) (vectorRecursion s β t p j) x‖ ≤
      Real.sqrt (n : ℝ)*(r.factorial : ℝ)*K^r := by
  have hh := normalizedExponentialExpectation_jets N (vectorTailGaussianBase n j)
    (fun x z => vectorTailPosteriorLogDensity s β t p x j z) (fun z => spinVector z.2)
    K (Real.sqrt (n : ℝ)) hK
    (fun z => ((contDiff_vectorTailPosteriorLogDensity_initial_noise s β t p j z.2).comp
      (contDiff_id.prodMk contDiff_const)).of_le (by simp))
    ⟨(2*Real.sqrt (n : ℝ)).toNNReal,fun z => vectorTailPosteriorLogDensity_lipschitz s β t p j hj z⟩
    (fun i hi hiN x z => hB i hi hiN j hj x z)
    (fun z => (norm_spinVector z.2).le)
    (fun i _ x => aestronglyMeasurable_vectorTailPosterior_exponentialJet s β t p j i x)
    (fun x => integrable_vectorTailPosterior_exp s β t p x j hj)
    (fun x => integral_vectorTailPosterior_exp s β t p x j hj)
  have he : (fun y => ∫z,Real.exp (vectorTailPosteriorLogDensity s β t p y j z) • spinVector z.2
      ∂vectorTailGaussianBase n j)=gradient (vectorRecursion s β t p j) := by
    funext y
    rw [integral_vectorTailPosterior_exp_spinVector s β t p y j hj,
      vectorMagnetization_eq_gradient]
  rw [←norm_iteratedFDeriv_gradient,←he]
  exact hh.2 r hr x

def vectorThirdJetBound (n : ℕ) : ℝ := 8*(n : ℝ)*Real.sqrt (n : ℝ)
def vectorFourthJetBound (n : ℕ) : ℝ := 48*(n : ℝ)^2

theorem norm_vectorRecursion_thirdJet_le (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (j : ℕ) (hj : j ≤ k+2) (x : Field n) :
    ‖iteratedFDeriv ℝ 3 (vectorRecursion s β t p j) x‖ ≤ vectorThirdJetBound n := by
  have hB (i : ℕ) (hi : 1 ≤ i) (hiN : i ≤ 2) (j : ℕ) (hj : j ≤ k+2)
      (x : Field n) (z : (Fin j → Field n) × Configuration n) :
      ‖iteratedFDeriv ℝ i (fun y => vectorTailPosteriorLogDensity s β t p y j z) x‖ ≤
        (2*Real.sqrt (n : ℝ))^i := by
    have hs := Real.sq_sqrt (Nat.cast_nonneg n)
    rcases (show i=1 ∨ i=2 by omega) with rfl | rfl
    · simpa only [pow_one] using norm_vectorTailLogDensity_firstJet_le s β t p j hj x z
    · exact (norm_vectorTailLogDensity_secondJet_le s β t p j hj x z).trans (by
        rw [mul_pow,hs]
        nlinarith [show 0 ≤ (n : ℝ) by positivity])
  have hh := norm_vectorRecursion_jet_from_tailScore s β t p 2 (2*Real.sqrt (n : ℝ))
    (by positivity) hB j hj 2 (by omega) x
  have he : Real.sqrt (n : ℝ)*((2 : ℕ).factorial : ℝ)*(2*Real.sqrt (n : ℝ))^2=
      vectorThirdJetBound n := by
    rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg n)]
    norm_num [vectorThirdJetBound,Nat.factorial]
    ring
  exact hh.trans_eq he

theorem norm_vectorTailLogDensity_thirdJet_le (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (j : ℕ) (hj : j ≤ k+2) (x : Field n)
    (z : (Fin j → Field n) × Configuration n) :
    ‖iteratedFDeriv ℝ 3 (fun y => vectorTailPosteriorLogDensity s β t p y j z) x‖ ≤
      vectorThirdJetBound n := by
  simpa only [zero_add] using norm_vectorTailLogDensity_jet_le s β t p 3 0
    (vectorThirdJetBound n) (by unfold vectorThirdJetBound;positivity)
    (fun j hj => norm_vectorRecursion_thirdJet_le s β t p j hj)
    (fun w x σ => by rw [vectorTerminalExponent_higherJet_zero β t p w x σ 3 (by omega),norm_zero])
    j hj x z

theorem norm_vectorRecursion_fourthJet_le (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (j : ℕ) (hj : j ≤ k+2) (x : Field n) :
    ‖iteratedFDeriv ℝ 4 (vectorRecursion s β t p j) x‖ ≤ vectorFourthJetBound n := by
  have hB (i : ℕ) (hi : 1 ≤ i) (hiN : i ≤ 3) (j : ℕ) (hj : j ≤ k+2)
      (x : Field n) (z : (Fin j → Field n) × Configuration n) :
      ‖iteratedFDeriv ℝ i (fun y => vectorTailPosteriorLogDensity s β t p y j z) x‖ ≤
        (2*Real.sqrt (n : ℝ))^i := by
    have hs := Real.sq_sqrt (Nat.cast_nonneg n)
    rcases (show i=1 ∨ i=2 ∨ i=3 by omega) with rfl | rfl | rfl
    · simpa only [pow_one] using norm_vectorTailLogDensity_firstJet_le s β t p j hj x z
    · exact (norm_vectorTailLogDensity_secondJet_le s β t p j hj x z).trans (by
        rw [mul_pow,hs]
        nlinarith [show 0 ≤ (n : ℝ) by positivity])
    · exact (norm_vectorTailLogDensity_thirdJet_le s β t p j hj x z).trans_eq (by
        unfold vectorThirdJetBound
        rw [pow_succ, mul_pow,hs]
        ring)
  have hh := norm_vectorRecursion_jet_from_tailScore s β t p 3 (2*Real.sqrt (n : ℝ))
    (by positivity) hB j hj 3 (by omega) x
  have he : Real.sqrt (n : ℝ)*((3 : ℕ).factorial : ℝ)*(2*Real.sqrt (n : ℝ))^3=
      vectorFourthJetBound n := by
    rw [pow_succ,mul_pow,Real.sq_sqrt (Nat.cast_nonneg n)]
    norm_num [vectorFourthJetBound,Nat.factorial]
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg n)]
  exact hh.trans_eq he

end QuantitativePaper
