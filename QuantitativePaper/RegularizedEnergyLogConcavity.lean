module
public import QuantitativePaper.RegularizedEnergyTail
public import FourPapersCommon.FiniteEuclideanPrekopaAll
public import FourPapersCommon.GaussianLebesgueDensity
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.Normed.Module.Convex

@[expose] public section

/-! Genuine log-concavity of the finite-SK exponential-regularized survival
function. Spin gauge invariance and the actual Gaussian density discharge
all Prékopa hypotheses, including zero-dimensional disorder. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace QuantitativePaper
open FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 1800000

def gaussianEnergyLinear (n : ℕ) (σ : Configuration n) : SKGaussianSpace n→L[ℝ]ℝ :=
  (1/Real.sqrt (n : ℝ)) • ∑e : Edge n,
    (Paper.spinSign (σ e.val.1)*Paper.spinSign (σ e.val.2)) • EuclideanSpace.proj e

theorem gaussianEnergyLinear_apply (n : ℕ) (σ : Configuration n) (z : SKGaussianSpace n) :
    gaussianEnergyLinear n σ z = energy n (skGaussianDisorderLinear n z) σ := by
  unfold gaussianEnergyLinear energy Paper.skHamiltonian
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,
    smul_eq_mul,zero_mul,add_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  change (Paper.spinSign (σ e.val.1)*Paper.spinSign (σ e.val.2))*z e=
    z e*Paper.spinSign (σ e.val.1)*Paper.spinSign (σ e.val.2)
  ring

def regularizedEnergyGaussianPotential (n : ℕ) (β : ℝ) (x : ℝ) (z : SKGaussianSpace n) : ℝ :=
  standardGaussianPotential z+β*max (energyFreeEnergy n β (skGaussianDisorderLinear n z)) x-
    β*gaussianEnergyLinear n (allPositiveConfiguration n) z

theorem convexOn_regularizedEnergyGaussianPotential (n : ℕ) (β : ℝ) (hβ : 0 < β) :
    ConvexOn ℝ (univ : Set (ℝ×SKGaussianSpace n))
      (Function.uncurry (regularizedEnergyGaussianPotential n β)) := by
  let sndL : ℝ×SKGaussianSpace n→ₗ[ℝ]SKGaussianSpace n := LinearMap.snd ℝ ℝ _
  let fstL : ℝ×SKGaussianSpace n→ₗ[ℝ]ℝ := LinearMap.fst ℝ ℝ _
  have hn : ConvexOn ℝ univ (fun z : SKGaussianSpace n=>‖z‖^2) :=
    convexOn_univ_norm.pow (fun _ _=>norm_nonneg _) 2
  have hg : ConvexOn ℝ univ (standardGaussianPotential (ι:=Edge n)) := by
    convert (hn.smul (show 0 ≤ (1/2 : ℝ) by norm_num)).add_const
      ((Fintype.card (Edge n) : ℝ)*Real.log (Real.sqrt (2*Real.pi))) using 1
    funext z
    simp only [standardGaussianPotential,smul_eq_mul,Pi.add_apply,Pi.smul_apply]
    ring
  have hx : ConvexOn ℝ univ
      (fun z : SKGaussianSpace n=>energyFreeEnergy n β (skGaussianDisorderLinear n z)) := by
    simpa only [energyFreeEnergy,smul_eq_mul,div_eq_mul_inv,mul_comm] using
      (convexOn_logPartition_gaussian n β).smul (inv_nonneg.mpr hβ.le)
  have hgs := hg.comp_linearMap sndL
  have hxs := hx.comp_linearMap sndL
  simp only [preimage_univ] at hgs hxs
  have hxf := (fstL.convexOn convex_univ)
  have hmax := (hxs.sup hxf).smul hβ.le
  have hlin := (-(β • (gaussianEnergyLinear n (allPositiveConfiguration n)).toLinearMap.comp sndL)).convexOn
    convex_univ
  convert (hgs.add hmax).add hlin using 1
  funext z
  change standardGaussianPotential z.2+β*max
    (energyFreeEnergy n β (skGaussianDisorderLinear n z.2)) z.1-
    β*gaussianEnergyLinear n (allPositiveConfiguration n) z.2 =
    standardGaussianPotential z.2+β*max
    (energyFreeEnergy n β (skGaussianDisorderLinear n z.2)) z.1+
    -(β*gaussianEnergyLinear n (allPositiveConfiguration n) z.2)
  ring

theorem regularizedEnergyGaussianPotential_exp (n : ℕ) (β x : ℝ) (z : SKGaussianSpace n) :
    Real.exp (-regularizedEnergyGaussianPotential n β x z) =
      standardGaussianEuclideanDensity z*
        regularizedEnergySpinTerm n β x (allPositiveConfiguration n) (skGaussianDisorderLinear n z) := by
  rw [regularizedEnergyGaussianPotential,regularizedEnergySpinTerm,
    ← exp_neg_standardGaussianPotential,gaussianEnergyLinear_apply,←Real.exp_add]
  congr 1
  ring

theorem integrable_standardGaussianEuclideanDensity_all_finite {ι : Type*} [Fintype ι] :
    Integrable (standardGaussianEuclideanDensity (ι:=ι)) (volume : Measure (EuclideanSpace ℝ ι)) := by
  have hm := measurable_standardGaussianEuclideanDensity (ι:=ι)
  rw [←(PiLp.volume_preserving_toLp ι).map_eq]
  apply (integrable_map_measure hm.aestronglyMeasurable (WithLp.measurable_toLp 2 _).aemeasurable).mpr
  exact integrable_standardGaussianProductDensity

theorem integrable_exp_neg_regularizedEnergyGaussianPotential (n : ℕ) (β x : ℝ) (hβ : 0 < β) :
    Integrable (fun z=>Real.exp (-regularizedEnergyGaussianPotential n β x z)) := by
  have hc : Continuous (fun z=>regularizedEnergyGaussianPotential n β x z) := by
    unfold regularizedEnergyGaussianPotential standardGaussianPotential energyFreeEnergy
    have hX := (continuous_logPartition n β).comp (skGaussianDisorderLinear n).continuous
    fun_prop
  apply integrable_standardGaussianEuclideanDensity_all_finite.mono' (Real.continuous_exp.comp hc.neg).aestronglyMeasurable
  filter_upwards with z
  change ‖Real.exp (-regularizedEnergyGaussianPotential n β x z)‖ ≤ _
  rw [Real.norm_of_nonneg (Real.exp_pos _).le,regularizedEnergyGaussianPotential_exp]
  have hg : 0 ≤ standardGaussianEuclideanDensity z := standardGaussianProductDensity_nonneg _
  exact (mul_le_mul_of_nonneg_left (regularizedEnergySpinTerm_le_one n β x hβ
    (allPositiveConfiguration n) _) hg).trans_eq (mul_one _)

 theorem integral_exp_neg_regularizedEnergyGaussianPotential (n : ℕ) (β x : ℝ) :
    (∫z : SKGaussianSpace n,Real.exp (-regularizedEnergyGaussianPotential n β x z)) =
      ∫g,regularizedEnergySpinTerm n β x (allPositiveConfiguration n) g ∂couplingLaw n := by
  have H := (hasLaw_skGaussianDisorder n).integral_comp
    (continuous_regularizedEnergySpinTerm n β x (allPositiveConfiguration n)).aestronglyMeasurable
  have hm : (stdGaussian (SKGaussianSpace n)) = SYK.standardGaussianMeasureOnEuclidean (Edge n) := by
    rw [←map_pi_eq_stdGaussian]
    rfl
  rw [hm,standardGaussianEuclidean_eq_withDensity,
    integral_withDensity_eq_integral_toReal_smul
      measurable_standardGaussianEuclideanDensity.ennreal_ofReal
      (.of_forall fun _=>ENNReal.ofReal_lt_top)] at H
  rw [←H]
  apply integral_congr_ae
  filter_upwards with z
  have hg : 0 ≤ standardGaussianEuclideanDensity z := standardGaussianProductDensity_nonneg _
  rw [ENNReal.toReal_ofReal hg,smul_eq_mul]
  exact regularizedEnergyGaussianPotential_exp n β x z

 theorem concaveOn_log_regularizedEnergyTail (n : ℕ) (β : ℝ) (hβ : 0 < β) :
    ConcaveOn ℝ univ (fun x=>Real.log (regularizedEnergyTail n β x)) := by
  have hc := concaveOn_log_integral_exp_neg_all_finite_euclidean
    (univ : Set ℝ) convex_univ (regularizedEnergyGaussianPotential n β)
    (by simpa only [univ_prod_univ] using convexOn_regularizedEnergyGaussianPotential n β hβ)
    (fun x _=>by
      unfold regularizedEnergyGaussianPotential standardGaussianPotential energyFreeEnergy
      have hX := (continuous_logPartition n β).comp (skGaussianDisorderLinear n).continuous
      fun_prop)
    (fun x _=>integrable_exp_neg_regularizedEnergyGaussianPotential n β x hβ)
  convert hc.add_const (Real.log ((2:ℝ)^n)) using 1
  funext x
  rw [regularizedEnergyTail_gauge_formula n β x hβ,
    ←integral_exp_neg_regularizedEnergyGaussianPotential]
  rw [Real.log_mul (by positivity) (ne_of_gt ?_)]
  · simp only [Pi.add_apply]
    ring
  · rw [integral_exp_neg_regularizedEnergyGaussianPotential]
    have ht := regularizedEnergyTail_pos n β x hβ.le
    rw [regularizedEnergyTail_gauge_formula n β x hβ] at ht
    have hp : 0 < (2:ℝ)^n := by positivity
    exact pos_of_mul_pos_right ht hp.le

end QuantitativePaper
