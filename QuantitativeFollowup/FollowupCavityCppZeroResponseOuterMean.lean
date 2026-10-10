module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseOuterNormalizer
public import QuantitativeFollowup.FollowupCavityCppZeroResponsePosteriorObservableJets
public import FourPapersCommon.ExponentialSmoothBounds

@[expose] public section

/-! Actual outer retained-observable expectations and their unnormalized
numerators. The numerator equals the true partition times the normalized
mean, and both are smooth with proved exponential jet envelopes. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology ContDiff BigOperators
namespace QuantitativeFollowup
variable {S J : Type} [Fintype S] [Nonempty S] [Fintype J]
  [MeasurableSpace S] [MeasurableSingletonClass S] {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

def cavityOuterPosteriorMean (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (s : ℝ) (N : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S)
    (f : FiniteStateField S→ℝ) (W : (Fin N→Field n)→L[ℝ]FiniteStateField S)
    (H : FiniteStateField S) : ℝ :=
  ∫p,f (H+R p.1+W p.2.1)∂cavityOuterPosteriorLaw V a L s N R H

def cavityOuterPosteriorWeightedMean (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (s : ℝ) (N : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S)
    (f : FiniteStateField S→ℝ) (W : (Fin N→Field n)→L[ℝ]FiniteStateField S)
    (H : FiniteStateField S) : ℝ :=
  ∫g,Real.exp (s*finiteStateGaussianTerminalCascade V a L N (H+R g))*
    cavityPosteriorTranslatedMean V a L N f (fun z=>W z.1) (H+R g)
    ∂stdGaussian (FiniteStateGaussianInput J)

theorem cavityOuterPosteriorMean_eq_weighted_div (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→Field n→L[ℝ]FiniteStateField S) (s : ℝ) (N : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S)
    (f : FiniteStateField S→ℝ) (hf : BoundedJets f)
    (W : (Fin N→Field n)→L[ℝ]FiniteStateField S) (H : FiniteStateField S) :
    cavityOuterPosteriorMean V a L s N R f W H=
      cavityOuterPosteriorWeightedMean V a L s N R f W H/
        cavityOuterPosteriorNormalizer V a L s N R H :=by
  haveI:=cavityOuterPosteriorLaw_probability V a ha L s N R H
  haveI:=cavityPosteriorGaussianKernel_markov V a ha L N
  obtain ⟨B,hB,hb⟩:=hf.2 0
  have hi:Integrable (fun p : FiniteStateGaussianInput J×((Fin N→Field n)×S)=>
      f (H+R p.1+W p.2.1)) (cavityOuterPosteriorLaw V a L s N R H):=
    (integrable_const B).mono' (hf.1.continuous.measurable.comp
      (show Measurable (fun p : FiniteStateGaussianInput J×((Fin N→Field n)×S)=>
        H+R p.1+W p.2.1) from by fun_prop)).aestronglyMeasurable
      (.of_forall fun p=>by simpa only [norm_iteratedFDeriv_zero] using hb (H+R p.1+W p.2.1))
  rw [cavityOuterPosteriorMean,cavityOuterPosteriorLaw,Measure.integral_compProd hi]
  simp_rw [Kernel.comap_apply,cavityPosteriorGaussianKernel_apply V a ha L N]
  rw [integral_tilted]
  simp only [smul_eq_mul,div_mul_eq_mul_div,integral_div]
  rw [←cavityOuterPosteriorNormalizer_eq_integral V a ha L s N R H]
  rfl

theorem cavityOuterPosteriorWeightedMean_eq_normalizer_mul (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→Field n→L[ℝ]FiniteStateField S) (s : ℝ) (N : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S)
    (f : FiniteStateField S→ℝ) (hf : BoundedJets f)
    (W : (Fin N→Field n)→L[ℝ]FiniteStateField S) (H : FiniteStateField S) :
    cavityOuterPosteriorWeightedMean V a L s N R f W H=
      cavityOuterPosteriorNormalizer V a L s N R H*cavityOuterPosteriorMean V a L s N R f W H :=by
  rw [cavityOuterPosteriorMean_eq_weighted_div V a ha L s N R f hf W H]
  have hZ : cavityOuterPosteriorNormalizer V a L s N R H ≠ 0 :=
    (finiteCascadeTreeGaussianNormalizer_pos V a ha L s N R H).ne'
  rw [mul_comm, div_mul_cancel₀ _ hZ]

theorem cavityOuterPosteriorWeightedMean_eq_gaussianWeightedShiftMoment
    (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (s : ℝ) (N : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S)
    (f : FiniteStateField S→ℝ) (hf : BoundedJets f)
    (W : (Fin N→Field n)→L[ℝ]FiniteStateField S) :
    cavityOuterPosteriorWeightedMean V a L s N R f W=
      gaussianWeightedShiftMoment (R.comp (cavityOuterGaussianCoordinates J)) s
        (finiteStateGaussianTerminalCascade V a L N)
        (cavityPosteriorTranslatedMean V a L N f (fun z=>W z.1)) :=by
  funext H
  let e:Field (Fintype.card J)≃ₗᵢ[ℝ]FiniteStateGaussianInput J:=
    (finiteStateGaussianBasis J).repr.symm
  have hm:Continuous (cavityPosteriorTranslatedMean V a L N f (fun z=>W z.1)):=
    (boundedJets_cavityPosteriorTranslatedMean V a ha ha1 hdec L N f hf W).1.continuous
  have hec:Continuous (fun g : FiniteStateGaussianInput J=>Real.exp
      (s*finiteStateGaussianTerminalCascade V a L N (H+R g))):=
    Real.continuous_exp.comp (((contDiff_finiteStateGaussianTerminalCascade V a ha L N).continuous.comp
      (continuous_const.add R.continuous)).const_mul s)
  have hcm : Continuous (fun g : FiniteStateGaussianInput J=>
      cavityPosteriorTranslatedMean V a L N f (fun z=>W z.1) (H+R g)) :=
    hm.comp ((continuous_const (y:=H)).add R.continuous)
  have hc : Continuous (fun g : FiniteStateGaussianInput J=>
      Real.exp (s*finiteStateGaussianTerminalCascade V a L N (H+R g))*
        cavityPosteriorTranslatedMean V a L N f (fun z=>W z.1) (H+R g)) := hec.mul hcm
  rw [cavityOuterPosteriorWeightedMean,←stdGaussian_map e,
    integral_map e.continuous.measurable.aemeasurable hc.aestronglyMeasurable]
  change _=∫z,Real.exp (s*finiteStateGaussianTerminalCascade V a L N
      (H+(R.comp (cavityOuterGaussianCoordinates J)) z))*
    cavityPosteriorTranslatedMean V a L N f (fun z=>W z.1)
      (H+(R.comp (cavityOuterGaussianCoordinates J)) z)∂fieldGaussian (Fintype.card J)
  rw [fieldGaussian_eq_stdGaussian]
  rfl

theorem contDiff_cavityOuterPosteriorWeightedMean (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (s : ℝ) (N : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S)
    (f : FiniteStateField S→ℝ) (hf : BoundedJets f)
    (W : (Fin N→Field n)→L[ℝ]FiniteStateField S) :
    ContDiff ℝ ∞ (cavityOuterPosteriorWeightedMean V a L s N R f W) :=by
  have hg:=boundedJets_cavityPosteriorTranslatedMean V a ha ha1 hdec L N f hf W
  choose G hG hgB using hg.2
  rw [cavityOuterPosteriorWeightedMean_eq_gaussianWeightedShiftMoment V a ha ha1 hdec L s N R f hf W]
  apply contDiff_infty.mpr
  intro r
  obtain ⟨hU,K,hK,hUB⟩:=finiteStateGaussianTerminalCascade_smooth_bounded_jets V a ha L r N
  exact contDiff_gaussianWeightedShiftMoment r _ _ hU (hg.1.of_le (by simp)) 1
    (finiteStateGaussianTerminalCascade_lipschitz V a ha L N) s K (zero_le_one.trans hK)
    G hG hUB (fun i _ H=>hgB i H) _

theorem contDiff_cavityOuterPosteriorMean (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (s : ℝ) (N : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S)
    (f : FiniteStateField S→ℝ) (hf : BoundedJets f)
    (W : (Fin N→Field n)→L[ℝ]FiniteStateField S) :
    ContDiff ℝ ∞ (cavityOuterPosteriorMean V a L s N R f W) :=by
  have he:cavityOuterPosteriorMean V a L s N R f W=
      fun H=>cavityOuterPosteriorWeightedMean V a L s N R f W H/
        cavityOuterPosteriorNormalizer V a L s N R H:=
    funext (cavityOuterPosteriorMean_eq_weighted_div V a ha L s N R f hf W)
  rw [he]
  exact (contDiff_cavityOuterPosteriorWeightedMean V a ha ha1 hdec L s N R f hf W).div
    (contDiff_cavityOuterPosteriorNormalizer V a ha L s N R)
    (fun H=>(finiteCascadeTreeGaussianNormalizer_pos V a ha L s N R H).ne')

theorem cavityOuterPosteriorWeightedMean_exponential_jets (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (s : ℝ) (N r : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S)
    (f : FiniteStateField S→ℝ) (hf : BoundedJets f)
    (W : (Fin N→Field n)→L[ℝ]FiniteStateField S) :
    ∃C:ℝ,0≤C ∧ ∀i,i≤r → ∀H : FiniteStateField S,
      ‖iteratedFDeriv ℝ i (cavityOuterPosteriorWeightedMean V a L s N R f W) H‖≤
        C*Real.exp (|s| *‖H‖) :=by
  obtain ⟨hU,K,hK,hUB⟩:=finiteStateGaussianTerminalCascade_smooth_bounded_jets V a ha L r N
  have hg:=boundedJets_cavityPosteriorTranslatedMean V a ha ha1 hdec L N f hf W
  choose G hG hgB using hg.2
  let B:=fun i=>gaussianWeightedJetCoefficient s K G i*
    cavityOuterPosteriorNormalizer V a L s N R 0
  let C:=∑i∈Finset.range (r+1),B i
  have hB0(i):0≤B i:=mul_nonneg
    (gaussianWeightedJetCoefficient_nonneg s K (zero_le_one.trans hK) G hG i)
    (finiteCascadeTreeGaussianNormalizer_pos V a ha L s N R 0).le
  refine ⟨C,Finset.sum_nonneg (fun i _=>hB0 i),?_⟩
  intro i hi H
  have hj:=norm_iteratedFDeriv_gaussianWeightedShiftMoment_le r i _ _ hU
    (hg.1.of_le (by simp)) 1 (finiteStateGaussianTerminalCascade_lipschitz V a ha L N)
    s K (zero_le_one.trans hK) G hG hUB (fun j _ Q=>hgB j Q)
    (R.comp (cavityOuterGaussianCoordinates J)) hi H
  rw [←cavityOuterPosteriorWeightedMean_eq_gaussianWeightedShiftMoment V a ha ha1 hdec L s N R f hf W,
    ←cavityOuterPosteriorNormalizer_eq_gaussianShiftPartition V a ha L s N R] at hj
  have hz:=cavityOuterPosteriorNormalizer_shift_bound V a ha L s N R H 0
  simp only [sub_zero] at hz
  have hm:=mul_le_mul_of_nonneg_left hz
    (gaussianWeightedJetCoefficient_nonneg s K (zero_le_one.trans hK) G hG i)
  have hb:B i≤C:=Finset.single_le_sum (fun j _=>hB0 j)
    (Finset.mem_range.mpr (by omega : i<r+1))
  have hlast := mul_le_mul_of_nonneg_right hb (Real.exp_pos (|s| * ‖H‖)).le
  apply hj.trans (hm.trans _)
  simpa only [B, mul_assoc, mul_comm, mul_left_comm] using hlast

theorem exponentialSmoothOn_cavityOuterPosteriorNormalizer (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→Field n→L[ℝ]FiniteStateField S) (s : ℝ) (N : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) :
    ExponentialSmoothOn (cavityOuterPosteriorNormalizer V a L s N R) univ :=by
  refine ⟨fun H _=>(contDiff_cavityOuterPosteriorNormalizer V a ha L s N R).contDiffAt,?_⟩
  intro r
  obtain ⟨C,hC,hb⟩:=cavityOuterPosteriorNormalizer_exponential_jets V a ha L s N r R
  exact ⟨C,|s|,hC,abs_nonneg s,fun H _=>hb r le_rfl H⟩

theorem exponentialSmoothOn_cavityOuterPosteriorWeightedMean (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (ha1 : a 0≤1) (hdec : Antitone a)
    (L : ℕ→Field n→L[ℝ]FiniteStateField S) (s : ℝ) (N : ℕ)
    (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S)
    (f : FiniteStateField S→ℝ) (hf : BoundedJets f)
    (W : (Fin N→Field n)→L[ℝ]FiniteStateField S) :
    ExponentialSmoothOn (cavityOuterPosteriorWeightedMean V a L s N R f W) univ :=by
  refine ⟨fun H _=>(contDiff_cavityOuterPosteriorWeightedMean V a ha ha1 hdec L s N R f hf W).contDiffAt,?_⟩
  intro r
  obtain ⟨C,hC,hb⟩:=cavityOuterPosteriorWeightedMean_exponential_jets V a ha ha1 hdec L s N r R f hf W
  exact ⟨C,|s|,hC,abs_nonneg s,fun H _=>hb r le_rfl H⟩

end QuantitativeFollowup
