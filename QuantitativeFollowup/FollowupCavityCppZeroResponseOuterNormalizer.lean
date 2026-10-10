module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseOuterLaw
public import FourPapersCommon.GenericFiniteStateCascadeVariance
public import QuantitativePaper.GaussianWeightedJets

@[expose] public section

/-! The actual outer partition is smooth in every retained-field direction.
Its positive jets have genuine exponential bounds; this includes the root
Gaussian tilt rather than just the conditional retained posterior. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology ContDiff
namespace QuantitativeFollowup
variable {S J : Type} [Fintype S] [Nonempty S] [Fintype J]
  [MeasurableSpace S] [MeasurableSingletonClass S] {n : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def cavityOuterGaussianCoordinates (J : Type) [Fintype J] :
    Field (Fintype.card J)→L[ℝ]FiniteStateGaussianInput J :=
  (finiteStateGaussianBasis J).repr.symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem cavityOuterPosteriorNormalizer_eq_gaussianShiftPartition (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→Field n→L[ℝ]FiniteStateField S) (s : ℝ) (N : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) :
    cavityOuterPosteriorNormalizer V a L s N R=
      gaussianShiftPartition (R.comp (cavityOuterGaussianCoordinates J)) s
        (finiteStateGaussianTerminalCascade V a L N) :=by
  funext H
  rw [cavityOuterPosteriorNormalizer_eq_integral V a ha L s N R H]
  let e:Field (Fintype.card J)≃ₗᵢ[ℝ]FiniteStateGaussianInput J :=
    (finiteStateGaussianBasis J).repr.symm
  have he:(stdGaussian (Field (Fintype.card J))).map e=
      stdGaussian (FiniteStateGaussianInput J):=stdGaussian_map e
  have hc:Continuous (fun g : FiniteStateGaussianInput J=>Real.exp
      (s*finiteStateGaussianTerminalCascade V a L N (H+R g))):=
    Real.continuous_exp.comp (((contDiff_finiteStateGaussianTerminalCascade V a ha L N).continuous.comp
      (continuous_const.add R.continuous)).const_mul s)
  rw [←he,integral_map e.continuous.measurable.aemeasurable
    hc.aestronglyMeasurable]
  change _=∫z,Real.exp (s*finiteStateGaussianTerminalCascade V a L N
    (H+(R.comp (cavityOuterGaussianCoordinates J)) z))∂fieldGaussian (Fintype.card J)
  rw [fieldGaussian_eq_stdGaussian]
  rfl

theorem contDiff_cavityOuterPosteriorNormalizer (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→Field n→L[ℝ]FiniteStateField S) (s : ℝ) (N : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) :
    ContDiff ℝ ∞ (cavityOuterPosteriorNormalizer V a L s N R) :=by
  rw [cavityOuterPosteriorNormalizer_eq_gaussianShiftPartition V a ha L s N R]
  apply contDiff_infty.mpr
  intro r
  obtain ⟨hf,K,hK,hB⟩:=finiteStateGaussianTerminalCascade_smooth_bounded_jets V a ha L r N
  exact contDiff_gaussianShiftPartition r _ hf 1
    (finiteStateGaussianTerminalCascade_lipschitz V a ha L N) K
    (zero_le_one.trans hK) hB _ s

theorem contDiff_log_cavityOuterPosteriorNormalizer (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→Field n→L[ℝ]FiniteStateField S) (s : ℝ) (N : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) :
    ContDiff ℝ ∞ (fun H=>Real.log (cavityOuterPosteriorNormalizer V a L s N R H)) :=
  (contDiff_cavityOuterPosteriorNormalizer V a ha L s N R).log
    (fun H=>(finiteCascadeTreeGaussianNormalizer_pos V a ha L s N R H).ne')

theorem cavityOuterPosteriorNormalizer_shift_bound (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→Field n→L[ℝ]FiniteStateField S) (s : ℝ) (N : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H Q : FiniteStateField S) :
    cavityOuterPosteriorNormalizer V a L s N R H≤
      Real.exp (|s| *‖H-Q‖)*cavityOuterPosteriorNormalizer V a L s N R Q :=by
  rw [cavityOuterPosteriorNormalizer_eq_integral V a ha L s N R H,
    cavityOuterPosteriorNormalizer_eq_integral V a ha L s N R Q,←integral_const_mul]
  apply integral_mono
    (integrable_exp_finiteStateGaussian_lipschitz _
      (finiteStateGaussianTerminalCascade_lipschitz V a ha L N) R H s)
    ((integrable_exp_finiteStateGaussian_lipschitz _
      (finiteStateGaussianTerminalCascade_lipschitz V a ha L N) R Q s).const_mul _)
  intro z
  dsimp only
  rw [←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hb:=(finiteStateGaussianTerminalCascade_lipschitz V a ha L N).norm_sub_le
    (H+R z) (Q+R z)
  simp only [Real.norm_eq_abs,NNReal.coe_one,one_mul,add_sub_add_right_eq_sub] at hb
  have hs:=mul_le_mul_of_nonneg_left hb (abs_nonneg s)
  have hh:=le_abs_self (s*(finiteStateGaussianTerminalCascade V a L N (H+R z)-
    finiteStateGaussianTerminalCascade V a L N (Q+R z)))
  rw [abs_mul] at hh
  linarith

theorem cavityOuterPosteriorNormalizer_exponential_jets (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→Field n→L[ℝ]FiniteStateField S) (s : ℝ) (N r : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) :
    ∃C:ℝ,0≤C ∧ ∀i,i≤r → ∀H : FiniteStateField S,
      ‖iteratedFDeriv ℝ i (cavityOuterPosteriorNormalizer V a L s N R) H‖≤
        C*Real.exp (|s| *‖H‖) :=by
  obtain ⟨hf,K,hK,hB⟩:=finiteStateGaussianTerminalCascade_smooth_bounded_jets V a ha L r N
  let B:=fun i=>gaussianJetCoefficient s K i*
    cavityOuterPosteriorNormalizer V a L s N R 0
  let C:=∑i∈Finset.range (r+1),B i
  have hB0(i):0≤B i:=mul_nonneg (gaussianJetCoefficient_nonneg s K (zero_le_one.trans hK) i)
    (finiteCascadeTreeGaussianNormalizer_pos V a ha L s N R 0).le
  refine ⟨C,Finset.sum_nonneg (fun i _=>hB0 i),?_⟩
  intro i hi H
  have hj:=norm_iteratedFDeriv_gaussianShiftPartition_le r i _ hf 1
    (finiteStateGaussianTerminalCascade_lipschitz V a ha L N) K (zero_le_one.trans hK)
    hB (R.comp (cavityOuterGaussianCoordinates J)) s hi H
  rw [←cavityOuterPosteriorNormalizer_eq_gaussianShiftPartition V a ha L s N R] at hj
  have hz:=cavityOuterPosteriorNormalizer_shift_bound V a ha L s N R H 0
  simp only [sub_zero] at hz
  have hm:=mul_le_mul_of_nonneg_left hz (gaussianJetCoefficient_nonneg s K (zero_le_one.trans hK) i)
  have hb:B i≤C:=Finset.single_le_sum (fun j _=>hB0 j)
    (Finset.mem_range.mpr (by omega : i<r+1))
  have hlast := mul_le_mul_of_nonneg_right hb (Real.exp_pos (|s| * ‖H‖)).le
  apply hj.trans (hm.trans _)
  simpa only [B, mul_assoc, mul_comm, mul_left_comm] using hlast

end QuantitativeFollowup
