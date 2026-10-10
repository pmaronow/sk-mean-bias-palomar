module
public import FourPapersCommon.MixedForkKernel

@[expose] public section

/-! The actual fork shares the selected state path up to its split. At split
zero its two magnetizations have the product of their actual one-point laws. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace FourPapersCommon
set_option maxHeartbeats 1000000

theorem parisiNoiseStatePath_causal (β h : ℝ) (μ : Paper.ParisiMeasure)
    (W Z : C(Icc (0 : ℝ) 1,ℝ)) (r : Paper.Overlap)
    (hWZ : ∀ t : Paper.Overlap, (t : ℝ) ≤ r → W t = Z t)
    (t : Paper.Overlap) (ht : (t : ℝ) ≤ r) :
    parisiNoiseStatePath β h μ W t = parisiNoiseStatePath β h μ Z t := by
  let v := fun s x => Paper.parisiGradient β μ (s,x)
  have he := Paper.parisiStateReal_causal β h μ v
    (Paper.continuous_parisiGradient β μ)
    (fun s x => Paper.norm_parisiGradient_le_one β μ (s,x))
    (Paper.lipschitzWith_parisiGradient_all β μ) 1 zero_le_one r.property
    (Paper.parisiNoiseExtension zero_le_one W) (Paper.parisiNoiseExtension zero_le_one Z)
    (Paper.continuous_parisiNoiseExtension zero_le_one W)
    (Paper.continuous_parisiNoiseExtension zero_le_one Z) (by
      intro s hs
      have hs1 : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1,hs.2.trans r.property.2⟩
      simpa only [Paper.parisiNoiseExtension, projIcc_of_mem zero_le_one hs1] using hWZ ⟨s,hs1⟩ hs.2)
      ⟨t.property.1,ht⟩
  exact (Paper.parisiStatePath_apply β h μ v (Paper.continuous_parisiGradient β μ)
    (fun s x => Paper.norm_parisiGradient_le_one β μ (s,x))
    (Paper.lipschitzWith_parisiGradient_all β μ) 1 zero_le_one W t).trans
      (he.trans (Paper.parisiStatePath_apply β h μ v (Paper.continuous_parisiGradient β μ)
        (fun s x => Paper.norm_parisiGradient_le_one β μ (s,x))
        (Paper.lipschitzWith_parisiGradient_all β μ) 1 zero_le_one Z t).symm)

def mixedForkState (ξ : AdmissibleEvenMixture) (h : ℝ) (μ : Paper.ParisiMeasure)
    (r q : Paper.Overlap) (sample : BrownianPair) : ℝ :=
  parisiNoiseStatePath (mixedBeta ξ) h (mixedMeasure ξ μ)
    (forkBrownianPath (ξ.clock r).toNNReal sample) (ξ.unitClock q)

theorem mixedForkState_before (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ : Paper.ParisiMeasure) (r q : Paper.Overlap) (hqr : (q : ℝ) ≤ r) (sample : BrownianPair) :
    mixedForkState ξ h μ r q sample = mixedState ξ h μ sample.1 q := by
  have hc : (ξ.unitClock q : ℝ) ≤ ξ.unitClock r := ξ.strictMono_unitClock.monotone hqr
  have he := parisiNoiseStatePath_causal (mixedBeta ξ) h (mixedMeasure ξ μ)
    (forkBrownianPath (ξ.clock r).toNNReal sample) (Paper.canonicalBrownianPath sample.1)
      (ξ.unitClock r) (by
        intro t ht
        apply forkBrownianPath_before
        exact Real.toNNReal_le_toNNReal ht) (ξ.unitClock q) hc
  exact he.trans (parisiNoiseStatePath_canonical (mixedBeta ξ) h (mixedBeta_ne_zero ξ)
    (mixedMeasure ξ μ) sample.1 (ξ.unitClock q))

theorem mixedForkMagnetization_before (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ : Paper.ParisiMeasure) (r q : Paper.Overlap) (hqr : (q : ℝ) ≤ r) (sample : BrownianPair) :
    (mixedForkMagnetization ξ h μ r q sample).2 = (mixedForkMagnetization ξ h μ r q sample).1 := by
  exact congrArg (fun x => mixedGradient ξ μ ((q : ℝ),x))
    (mixedForkState_before ξ h μ r q hqr sample)

theorem mixedForkLaw_zero (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) :
    (mixedForkLaw ξ h μ ⟨0, by norm_num⟩ q : Measure (ℝ×ℝ)) =
      (mixedMagnetizationLaw ξ h μ q : Measure ℝ).prod (mixedMagnetizationLaw ξ h μ q : Measure ℝ) := by
  change brownianPairMeasure.map (mixedForkMagnetization ξ h μ ⟨0,by norm_num⟩ q) =
    (Paper.canonicalBrownianMeasure.map (mixedMagnetization ξ h μ q)).prod
      (Paper.canonicalBrownianMeasure.map (mixedMagnetization ξ h μ q))
  rw [Measure.map_prod_map _ _ (measurable_mixedMagnetization ξ h μ q)
    (measurable_mixedMagnetization ξ h μ q)]
  congr 1
  funext sample
  change (_,mixedNoiseMagnetization ξ h μ q (forkBrownianPath (ξ.clock 0).toNNReal sample)) = _
  simp only [ξ.clock_zero, Real.toNNReal_zero, forkBrownianPath_zero,
    mixedNoiseMagnetization_canonical]
  rfl

end FourPapersCommon
