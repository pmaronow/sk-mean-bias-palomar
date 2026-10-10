module
public import QuantitativeFollowup.FollowupCavityPhysicalRowLaw
public import FourPapersCommon.FiniteCascadeTreeGaussianRowResponse

@[expose] public section

/-! Actual incident-coupling variance response. The physical coupling is
sqrt(v) times a genuine standard Gaussian disorder coordinate; the
auxiliary-field variances and all remaining couplings stay fixed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
open scoped Topology BigOperators
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 2600000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def anisotropicReplaceCouplingVariance (D : AnisotropicSpinModel n)
    (e : AnisotropicCouplingIndex n) (v : ℝ) : AnisotropicSpinModel n where
  variance := D.variance
  variance_pos := D.variance_pos
  coupling f := if f = e then Real.sqrt v else D.coupling f

theorem anisotropicRemoveCoupling_replaceVariance (D : AnisotropicSpinModel n)
    (e : AnisotropicCouplingIndex n) (v : ℝ) :
    anisotropicRemoveCoupling (anisotropicReplaceCouplingVariance D e v) e =
      anisotropicRemoveCoupling D e := by
  unfold anisotropicRemoveCoupling anisotropicReplaceCouplingVariance
  congr 1
  funext f
  split_ifs <;> simp_all

theorem anisotropicEnergyInputs_replaceCouplingVariance (D : AnisotropicSpinModel n)
    (e : AnisotropicCouplingIndex n) (v : ℝ) (s : RSBScheme k) (j : ℕ) :
    (anisotropicEnergyMap (anisotropicReplaceCouplingVariance D e v)).comp
        (anisotropicSchemeInput (anisotropicReplaceCouplingVariance D e v) s j) =
      (anisotropicEnergyMap D).comp (anisotropicSchemeInput D s j) := by
  ext z σ
  simp only [ContinuousLinearMap.comp_apply, anisotropicSchemeInput_apply,
    anisotropicEnergyMap_apply, anisotropicFieldInjection_apply,
    anisotropicTerminalLinear_apply, anisotropicHamiltonian, PiLp.zero_apply,
    mul_zero, zero_mul, Finset.sum_const_zero, zero_add]
  rfl

def anisotropicCouplingVarianceRowLaw (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (e : AnisotropicCouplingIndex n)
    (T : FiniteTerminalGenealogy (k+2)) (v : ℝ) :=
  finiteCascadeTreeGaussianRowLaw (fun _ : Configuration n => 0) (anisotropicCouplingFeature e)
    (anisotropicSchemeMass s)
    (fun j => (anisotropicEnergyMap D).comp (anisotropicSchemeInput D s j)) a v
    (trimRoot T) (anisotropicRootEnergyMap (anisotropicRemoveCoupling D e)) 0

def anisotropicCouplingVarianceRowCurvature (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (e : AnisotropicCouplingIndex n)
    (T : FiniteTerminalGenealogy (k+2)) :=
  finiteCascadeTreeGaussianRowCurvature (fun _ : Configuration n => 0) (anisotropicCouplingFeature e)
    (anisotropicSchemeMass s)
    (fun j => (anisotropicEnergyMap D).comp (anisotropicSchemeInput D s j)) a (trimRoot T)

def anisotropicCouplingRowObservable (T : FiniteTerminalGenealogy (k+2))
    (F : FiniteCascadeGenealogy.Samples (Configuration n) (asGenealogy T) → ℝ) :=
  fun z : FiniteStateField (Configuration n) ×
      Records (FiniteStateField (Configuration n)) (Configuration n) (trimRoot T) =>
    F ((trimmedSpinEquiv (S:=Configuration n) T) (spins (trimRoot T) z.2))

theorem integral_anisotropicTreeLaw_coupling_variance (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (ha : a ≤ s.m 1) (hq : s.q 1 = 0)
    (e : AnisotropicCouplingIndex n) (T : FiniteTerminalGenealogy (k+2))
    (v : ℝ) (hv : 0 ≤ v)
    (F : FiniteCascadeGenealogy.Samples (Configuration n) (asGenealogy T) → ℝ)
    (hF : Measurable F) (C : ℝ) (hC : 0 ≤ C) (hFb : ∀z,|F z| ≤ C) :
    (∫σ,F σ ∂anisotropicFiniteTreeLaw (anisotropicReplaceCouplingVariance D e v) s a (asGenealogy T)) =
      ∫z,anisotropicCouplingRowObservable T F z.2 ∂anisotropicCouplingVarianceRowLaw D s a e T v := by
  have he := integral_anisotropicFiniteCouplingRowLaw_spins
    (anisotropicReplaceCouplingVariance D e v) s a ha hq e T F hF C hC hFb
  rw [← he]
  congr 1
  unfold anisotropicFiniteCouplingRowLaw anisotropicCouplingVarianceRowLaw
  rw [show (fun j => (anisotropicEnergyMap (anisotropicReplaceCouplingVariance D e v)).comp
      (anisotropicSchemeInput (anisotropicReplaceCouplingVariance D e v) s j)) =
      (fun j => (anisotropicEnergyMap D).comp (anisotropicSchemeInput D s j)) from
        funext (anisotropicEnergyInputs_replaceCouplingVariance D e v s),
    anisotropicRemoveCoupling_replaceVariance]
  congr 1
  simp only [anisotropicReplaceCouplingVariance, ite_true, Real.sq_sqrt hv]

theorem hasDerivAt_anisotropicFiniteTreeLaw_coupling_variance (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (ha : a ≤ s.m 1) (hq : s.q 1 = 0)
    (e : AnisotropicCouplingIndex n) (T : FiniteTerminalGenealogy (k+2))
    (v : ℝ) (hv : 0 < v)
    (F : FiniteCascadeGenealogy.Samples (Configuration n) (asGenealogy T) → ℝ)
    (hF : Measurable F) (C : ℝ) (hC : 0 ≤ C) (hFb : ∀z,|F z| ≤ C) :
    HasDerivAt (fun u => ∫σ,F σ ∂anisotropicFiniteTreeLaw
      (anisotropicReplaceCouplingVariance D e u) s a (asGenealogy T))
      ((1/2:ℝ) * ((∫z,anisotropicCouplingRowObservable T F z.2 *
        anisotropicCouplingVarianceRowCurvature D s a e T z
          ∂anisotropicCouplingVarianceRowLaw D s a e T v) -
        (∫z,anisotropicCouplingRowObservable T F z.2
          ∂anisotropicCouplingVarianceRowLaw D s a e T v) *
        (∫z,anisotropicCouplingVarianceRowCurvature D s a e T z
          ∂anisotropicCouplingVarianceRowLaw D s a e T v))) v := by
  have hm : Measurable (anisotropicCouplingRowObservable T F) :=
    hF.comp ((trimmedSpinEquiv (S:=Configuration n) T).measurable.comp
      ((measurable_spins (trimRoot T)).comp measurable_snd))
  have hd := hasDerivAt_finiteCascadeTreeGaussianRowExpectation_variance
    (fun _ : Configuration n => 0) (anisotropicCouplingFeature e)
    (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s)
    (anisotropicSchemeMass_antitone s) (anisotropicSchemeMass_le_one s 0)
    (fun j => (anisotropicEnergyMap D).comp (anisotropicSchemeInput D s j)) a v hv
    (trimRoot T) (anisotropicTrimmedTreeRootCoefficient_le s a ha T)
    (anisotropicRootEnergyMap (anisotropicRemoveCoupling D e)) 0 1 (by norm_num)
    (fun σ => by simp [anisotropicCouplingFeature_apply, abs_mul, Paper.abs_spinSign])
    (anisotropicCouplingRowObservable T F) hm C hC (fun z => hFb _)
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hv] with u hu
  exact integral_anisotropicTreeLaw_coupling_variance D s a ha hq e T u hu.le F hF C hC hFb

end QuantitativeFollowup
