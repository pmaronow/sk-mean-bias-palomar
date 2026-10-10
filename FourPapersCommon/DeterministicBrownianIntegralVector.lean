module
public import FourPapersCommon.DeterministicBrownianIntegral
public import Mathlib.Probability.Distributions.Gaussian.CharFun

@[expose] public section

/-! Actual finite joint Gaussian laws of genuine deterministic Wiener
integrals. Linearity proves every scalar projection is Gaussian. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory StochasticCalculus
open scoped Topology BigOperators NNReal
namespace FourPapersCommon
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0→Ω→ℝ}
set_option maxHeartbeats 1000000

def deterministicWienerVector {J : Type*} [Fintype J]
    (hB : IsPreBrownianReal B P) (f : J→Lp ℝ 2 nonnegativeLebesgueMeasure)
    (ω : Ω) : EuclideanSpace ℝ J :=
  WithLp.toLp 2 (fun j=>(wienerIntegral hB (f j) : Ω→ℝ) ω)

theorem measurable_deterministicWienerVector {J : Type*} [Fintype J]
    (hB : IsPreBrownianReal B P) (f : J→Lp ℝ 2 nonnegativeLebesgueMeasure) :
    Measurable (deterministicWienerVector hB f) := by
  unfold deterministicWienerVector
  apply (PiLp.continuous_toLp 2 (fun _ : J=>ℝ)).measurable.comp
  apply Measurable.of_eval
  intro j
  exact (Lp.stronglyMeasurable (wienerIntegral hB (f j))).measurable

theorem deterministicWiener_sum_ae_eq {J : Type*} [Fintype J]
    (hB : IsPreBrownianReal B P) (f : J→Lp ℝ 2 nonnegativeLebesgueMeasure)
    (c : J→ℝ) :
    (fun ω=>∑j:J,c j*(wienerIntegral hB (f j) : Ω→ℝ) ω)=ᵐ[P]
      (wienerIntegral hB (∑j:J,c j • f j) : Ω→ℝ) := by
  have hm : wienerIntegral hB (∑j:J,c j • f j)=∑j:J,c j • wienerIntegral hB (f j) := by
    rw [map_sum]
    exact Finset.sum_congr rfl (fun j _=>(wienerIntegral hB).map_smul _ _)
  rw [hm]
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun j=>c j • wienerIntegral hB (f j)),
    ae_all_iff.mpr (fun j:J=>Lp.coeFn_smul (c j) (wienerIntegral hB (f j)))] with ω hs hi
  rw [hs]
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl (fun j _=>(hi j).symm)

theorem hasGaussianLaw_deterministicWienerVector {J : Type*} [Fintype J]
    (hB : IsPreBrownianReal B P) (f : J→Lp ℝ 2 nonnegativeLebesgueMeasure) :
    HasGaussianLaw (deterministicWienerVector hB f) P := by
  apply (hasGaussianLaw_iff_charFun_map_eq (measurable_deterministicWienerVector hB f).aemeasurable).mpr
  intro t
  have he : (fun ω=>inner ℝ (deterministicWienerVector hB f ω) t)=
      (fun ω=>∑j:J,t j*(wienerIntegral hB (f j) : Ω→ℝ) ω) := by
    funext ω
    simp [deterministicWienerVector,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,mul_comm]
  have hg : HasGaussianLaw (fun ω=>inner ℝ (deterministicWienerVector hB f ω) t) P := by
    rw [he]
    exact (hasGaussianLaw_wienerIntegral hB (∑j:J,t j • f j)).congr
      (deterministicWiener_sum_ae_eq hB f (fun j=>t j)).symm
  rw [charFun_map_eq_charFun_map_inner_one (measurable_deterministicWienerVector hB f).aemeasurable]
  simpa only [RCLike.inner_apply,starRingEnd_apply,star_trivial,one_mul,mul_one,real_inner_comm] using
    hg.charFun_map_eq (1:ℝ)

theorem covariance_deterministicWiener (hB : IsPreBrownianReal B P)
    (f g : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    cov[(wienerIntegral hB f : Ω→ℝ),(wienerIntegral hB g : Ω→ℝ);P]=inner ℝ f g := by
  unfold covariance
  rw [integral_wienerIntegral hB f,integral_wienerIntegral hB g]
  simp only [sub_zero]
  rw [←inner_wienerIntegral hB f g,L2.inner_def]
  apply integral_congr_ae
  exact ae_of_all _ (fun ω=>by simp only [RCLike.inner_apply,starRingEnd_apply,star_trivial];ring)

theorem isGaussianProcess_deterministicWiener
    (hB : IsPreBrownianReal B P) (f : ℝ≥0 → Lp ℝ 2 nonnegativeLebesgueMeasure) :
    IsGaussianProcess (fun t ω => (wienerIntegral hB (f t) : Ω → ℝ) ω) P := by
  constructor
  intro I
  have H := hasGaussianLaw_deterministicWienerVector hB (fun i : I => f i)
  exact H.map (PiLp.continuousLinearEquiv 2 ℝ (fun _ : I => ℝ)).toContinuousLinearMap

end FourPapersCommon
