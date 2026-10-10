module
public import FourPapersCommon.BrownianClockRescaling
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Moments.Covariance

public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

public import Mathlib.Probability.Distributions.Gaussian.Fernique

@[expose] public section

/-! A concrete Brownian fork on two independent copies of the constructed
Brownian probability space.  The second driver follows the first up to the
split and uses the independent second driver's increments thereafter. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal Topology ProbabilityTheory
namespace FourPapersCommon

abbrev BrownianPair := Paper.BrownianSample × Paper.BrownianSample

def brownianPairMeasure : Measure BrownianPair :=
  Paper.canonicalBrownianMeasure.prod Paper.canonicalBrownianMeasure

instance : IsProbabilityMeasure brownianPairMeasure := by
  unfold brownianPairMeasure
  infer_instance

def forkBrownian (r t : ℝ≥0) (sample : BrownianPair) : ℝ :=
  Paper.canonicalBrownian (min t r) sample.1 + Paper.canonicalBrownian t sample.2 -
    Paper.canonicalBrownian (min t r) sample.2

theorem measurable_forkBrownian (r t : ℝ≥0) : Measurable (forkBrownian r t) := by
  unfold forkBrownian
  exact (((Paper.measurable_canonicalBrownian _).comp measurable_fst).add
    ((Paper.measurable_canonicalBrownian _).comp measurable_snd)).sub
      ((Paper.measurable_canonicalBrownian _).comp measurable_snd)

theorem continuous_forkBrownian (r : ℝ≥0) (sample : BrownianPair) :
    Continuous (fun t => forkBrownian r t sample) := by
  unfold forkBrownian
  exact (((Paper.continuous_canonicalBrownian sample.1).comp
    (continuous_id.min continuous_const)).add
    (Paper.continuous_canonicalBrownian sample.2)).sub
      ((Paper.continuous_canonicalBrownian sample.2).comp
        (continuous_id.min continuous_const))

theorem continuous_forkBrownian_split_time (sample : BrownianPair) :
    Continuous (fun p : ℝ≥0 × ℝ≥0 => forkBrownian p.1 p.2 sample) := by
  unfold forkBrownian
  exact (((Paper.continuous_canonicalBrownian sample.1).comp
    (continuous_snd.min continuous_fst)).add
    ((Paper.continuous_canonicalBrownian sample.2).comp continuous_snd)).sub
      ((Paper.continuous_canonicalBrownian sample.2).comp
        (continuous_snd.min continuous_fst))

@[simp] theorem forkBrownian_zero (r : ℝ≥0) (sample : BrownianPair) :
    forkBrownian r 0 sample = 0 := by simp [forkBrownian]

theorem forkBrownian_before (r t : ℝ≥0) (ht : t ≤ r) (sample : BrownianPair) :
    forkBrownian r t sample = Paper.canonicalBrownian t sample.1 := by
  simp [forkBrownian, min_eq_left ht]

theorem forkBrownian_after (r t : ℝ≥0) (ht : r ≤ t) (sample : BrownianPair) :
    forkBrownian r t sample = Paper.canonicalBrownian r sample.1 +
      (Paper.canonicalBrownian t sample.2 - Paper.canonicalBrownian r sample.2) := by
  simp only [forkBrownian, min_eq_right ht]
  ring

private theorem fork_brownian_gaussian (r : ℝ≥0) :
    IsGaussianProcess (forkBrownian r) brownianPairMeasure := by
  classical
  constructor
  intro I
  let J := I ∪ I.image (fun t => min t r)
  let X : Paper.BrownianSample → J → ℝ := fun sample => J.restrict
    (fun t => Paper.canonicalBrownian t sample)
  have hX : Measurable X := Measurable.of_eval fun j => Paper.measurable_canonicalBrownian j
  have hG := Paper.isBrownianReal_canonicalBrownian.toIsPreBrownianReal.hasLaw J
  have hG1 : HasGaussianLaw (fun sample : BrownianPair => X sample.1) brownianPairMeasure :=
    (hG.comp measurePreserving_fst.hasLaw).hasGaussianLaw
  have hG2 : HasGaussianLaw (fun sample : BrownianPair => X sample.2) brownianPairMeasure :=
    (hG.comp measurePreserving_snd.hasLaw).hasGaussianLaw
  have hi : IndepFun (fun sample : BrownianPair => X sample.1)
      (fun sample : BrownianPair => X sample.2) brownianPairMeasure :=
    indepFun_prod hX hX
  let L : ((J → ℝ) × (J → ℝ)) →L[ℝ] I → ℝ :=
    { toFun z t := z.1 ⟨min t r, by exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨t, t.property, rfl⟩)⟩ +
        z.2 ⟨t, by simp [J, t.property]⟩ -
        z.2 ⟨min t r, by exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨t, t.property, rfl⟩)⟩
      map_add' z w := by ext t; simp; ring
      map_smul' a z := by ext t; simp; ring }
  exact (hi.hasGaussianLaw hG1 hG2).map L

private theorem brownian_pair_memLp_fst (t : ℝ≥0) :
    MemLp (fun sample : BrownianPair => Paper.canonicalBrownian t sample.1) 2 brownianPairMeasure :=
  (Paper.isBrownianReal_canonicalBrownian.toIsPreBrownianReal.isGaussianProcess.hasGaussianLaw_eval t).memLp_two.comp_fst _

private theorem brownian_pair_memLp_snd (t : ℝ≥0) :
    MemLp (fun sample : BrownianPair => Paper.canonicalBrownian t sample.2) 2 brownianPairMeasure :=
  (Paper.isBrownianReal_canonicalBrownian.toIsPreBrownianReal.isGaussianProcess.hasGaussianLaw_eval t).memLp_two.comp_snd _

theorem integral_forkBrownian (r t : ℝ≥0) :
    ∫ sample, forkBrownian r t sample ∂brownianPairMeasure = 0 := by
  let A : BrownianPair → ℝ := fun sample => Paper.canonicalBrownian (min t r) sample.1
  let B : BrownianPair → ℝ := fun sample => Paper.canonicalBrownian t sample.2
  let C : BrownianPair → ℝ := fun sample => Paper.canonicalBrownian (min t r) sample.2
  change (∫ sample, (A + B - C) sample ∂brownianPairMeasure) = (0 : ℝ)
  have hAi : Integrable A brownianPairMeasure := (brownian_pair_memLp_fst (min t r)).integrable (by norm_num)
  have hBi : Integrable B brownianPairMeasure := (brownian_pair_memLp_snd t).integrable (by norm_num)
  have hCi : Integrable C brownianPairMeasure := (brownian_pair_memLp_snd (min t r)).integrable (by norm_num)
  simp only [Pi.sub_apply, Pi.add_apply]
  have hadd : Integrable (fun sample => A sample + B sample) brownianPairMeasure := hAi.add hBi
  rw [integral_sub hadd hCi, integral_add hAi hBi]
  dsimp only [A, B, C]
  have hB := Paper.isBrownianReal_canonicalBrownian.toIsPreBrownianReal
  have hf (v : ℝ≥0) : (∫ sample : BrownianPair, Paper.canonicalBrownian v sample.1
      ∂brownianPairMeasure) = 0 := by
    have hp : HasLaw (Prod.fst : BrownianPair → Paper.BrownianSample)
        Paper.canonicalBrownianMeasure brownianPairMeasure := measurePreserving_fst.hasLaw
    simpa only [Function.comp_def, hB.integral_eval] using
      hp.integral_comp (Paper.measurable_canonicalBrownian v).aestronglyMeasurable
  have hs (v : ℝ≥0) : (∫ sample : BrownianPair, Paper.canonicalBrownian v sample.2
      ∂brownianPairMeasure) = 0 := by
    have hp : HasLaw (Prod.snd : BrownianPair → Paper.BrownianSample)
        Paper.canonicalBrownianMeasure brownianPairMeasure := measurePreserving_snd.hasLaw
    simpa only [Function.comp_def, hB.integral_eval] using
      hp.integral_comp (Paper.measurable_canonicalBrownian v).aestronglyMeasurable
  rw [hf, hs, hs]
  ring

theorem covariance_forkBrownian (r s t : ℝ≥0) :
    cov[forkBrownian r s, forkBrownian r t; brownianPairMeasure] = (min s t : ℝ≥0) := by
  let A : ℝ≥0 → BrownianPair → ℝ := fun t sample => Paper.canonicalBrownian t sample.1
  let B : ℝ≥0 → BrownianPair → ℝ := fun t sample => Paper.canonicalBrownian t sample.2
  have hA := brownian_pair_memLp_fst
  have hB := brownian_pair_memLp_snd
  have hAA (a b : ℝ≥0) : cov[A a, A b; brownianPairMeasure] = (min a b : ℝ≥0) := by
    change cov[fun sample : BrownianPair => Paper.canonicalBrownian a sample.1,
      fun sample => Paper.canonicalBrownian b sample.1;
      Paper.canonicalBrownianMeasure.prod Paper.canonicalBrownianMeasure] = _
    rw [measurePreserving_fst.hasLaw.covariance_fun_comp
      (Paper.measurable_canonicalBrownian _).aemeasurable
      (Paper.measurable_canonicalBrownian _).aemeasurable]
    exact Paper.isBrownianReal_canonicalBrownian.toIsPreBrownianReal.covariance_eval a b
  have hBB (a b : ℝ≥0) : cov[B a, B b; brownianPairMeasure] = (min a b : ℝ≥0) := by
    change cov[fun sample : BrownianPair => Paper.canonicalBrownian a sample.2,
      fun sample => Paper.canonicalBrownian b sample.2;
      Paper.canonicalBrownianMeasure.prod Paper.canonicalBrownianMeasure] = _
    rw [measurePreserving_snd.hasLaw.covariance_fun_comp
      (Paper.measurable_canonicalBrownian _).aemeasurable
      (Paper.measurable_canonicalBrownian _).aemeasurable]
    exact Paper.isBrownianReal_canonicalBrownian.toIsPreBrownianReal.covariance_eval a b
  have hAB (a b : ℝ≥0) : cov[A a, B b; brownianPairMeasure] = 0 :=
    covariance_fst_snd_prod
      (Paper.isBrownianReal_canonicalBrownian.toIsPreBrownianReal.isGaussianProcess.hasGaussianLaw_eval a).memLp_two
      (Paper.isBrownianReal_canonicalBrownian.toIsPreBrownianReal.isGaussianProcess.hasGaussianLaw_eval b).memLp_two
  have hBA (a b : ℝ≥0) : cov[B a, A b; brownianPairMeasure] = 0 := by
    rw [covariance_comm]; exact hAB b a
  change cov[A (min s r) + B s - B (min s r),
    A (min t r) + B t - B (min t r); brownianPairMeasure] = _
  rw [covariance_sub_left ((hA _).add (hB _)) (hB _) (((hA _).add (hB _)).sub (hB _)),
    covariance_sub_right ((hA _).add (hB _)) ((hA _).add (hB _)) (hB _),
    covariance_sub_right (hB _) ((hA _).add (hB _)) (hB _)]
  rw [covariance_add_left (hA _) (hB _) ((hA _).add (hB _)),
    covariance_add_right (hA _) (hA _) (hB _),
    covariance_add_right (hB _) (hA _) (hB _),
    covariance_add_left (hA _) (hB _) (hB _),
    covariance_add_right (hB _) (hA _) (hB _)]
  dsimp only [A, B] at hAA hBB hAB hBA
  simp only [hAA, hBB, hAB, hBA, add_zero, zero_add]
  have h1 : min (min s r) (min t r) = min (min s t) r := by
    simp only [min_assoc, min_left_comm, min_self]
  have h2 : min s (min t r) = min (min s t) r := (min_assoc _ _ _).symm
  have h3 : min (min s r) t = min (min s t) r := by
    rw [min_assoc, min_comm r t, ← min_assoc]
  rw [h1, h2, h3]
  ring

theorem isBrownianReal_forkBrownian (r : ℝ≥0) :
    IsBrownianReal (forkBrownian r) brownianPairMeasure := by
  refine ⟨(fork_brownian_gaussian r).isPreBrownianReal_of_covariance
    (integral_forkBrownian r) ?_, Filter.Eventually.of_forall (continuous_forkBrownian r)⟩
  intro s t hst
  simpa only [min_eq_left hst] using covariance_forkBrownian r s t

theorem forkBrownian_fullLaw (r : ℝ≥0) :
    brownianPairMeasure.map (fun sample => fun t => forkBrownian r t sample) =
      Paper.canonicalBrownianMeasure.map (fun sample => fun t => Paper.canonicalBrownian t sample) := by
  have hf := (isBrownianReal_forkBrownian r).toIsPreBrownianReal.hasLaw_gaussianLimit
    (Measurable.of_eval (measurable_forkBrownian r)).aemeasurable
  have hb := Paper.isBrownianReal_canonicalBrownian.toIsPreBrownianReal.hasLaw_gaussianLimit
    (Measurable.of_eval Paper.measurable_canonicalBrownian).aemeasurable
  exact hf.map_eq.trans hb.map_eq.symm

end FourPapersCommon
