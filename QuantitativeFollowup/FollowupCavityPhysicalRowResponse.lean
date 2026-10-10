module
public import QuantitativeFollowup.FollowupCavityRowVariance
public import QuantitativeFollowup.FollowupCavityPhysicalRowRecords
public import FourPapersCommon.FiniteCascadeIntrinsicRowCurvature

@[expose] public section

/-! The selected physical coupling-variance derivative is a covariance
under the actual retained cavity law, with its actual intrinsic density
curvature. No Gaussian row law remains in the final expectation. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def anisotropicIncidentCurvature (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (a : ℝ) (e : AnisotropicCouplingIndex n) (T : FiniteTerminalGenealogy (k+2)) :=
  finiteCascadeIntrinsicRowCurvature (fun _ : Configuration n => 0) (anisotropicCouplingFeature e)
    (anisotropicSchemeMass s)
    (fun j => (anisotropicEnergyMap D).comp (anisotropicSchemeInput D s j)) a (trimRoot T)

theorem measurable_anisotropicIncidentCurvature (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (e : AnisotropicCouplingIndex n)
    (T : FiniteTerminalGenealogy (k+2)) :
    Measurable (anisotropicIncidentCurvature D s a e T) :=
  measurable_finiteCascadeIntrinsicRowCurvature _ _ _ (anisotropicSchemeMass_nonneg s) _ _ _

theorem integral_anisotropicCouplingRowLaw_curvature_mul (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (ha : a ≤ s.m 1)
    (e : AnisotropicCouplingIndex n) (T : FiniteTerminalGenealogy (k+2))
    (F : FiniteCascadeGenealogy.Samples (Configuration n) (asGenealogy T) → ℝ)
    (hF : Measurable F) :
    (∫z,anisotropicCouplingRowObservable T F z.2 *
      anisotropicCouplingVarianceRowCurvature D s a e T z
        ∂anisotropicCouplingVarianceRowLaw D s a e T (D.coupling e^2)) =
      ∫z,anisotropicCouplingRowObservable T F z * anisotropicIncidentCurvature D s a e T z
        ∂anisotropicTrimmedRecordedTreeLaw D s a T := by
  have hf : Measurable (anisotropicCouplingRowObservable T F) :=
    hF.comp ((trimmedSpinEquiv (S:=Configuration n) T).measurable.comp
      ((measurable_spins (trimRoot T)).comp measurable_snd))
  have hm := measurable_finiteCascadeGaussianRowPhysicalRecords (anisotropicCouplingFeature e)
    (trimRoot T)
  have hi := integral_map (μ:=anisotropicFiniteCouplingRowLaw D s a e T) hm.aemeasurable
    (hf.mul (measurable_anisotropicIncidentCurvature D s a e T)).aestronglyMeasurable
  rw [anisotropicFiniteCouplingRowLaw_physical_records_map D s a ha e T] at hi
  simp only [Pi.mul_apply] at hi
  rw [hi]
  apply integral_congr_ae
  exact .of_forall fun z => by
    change anisotropicCouplingRowObservable T F z.2 *
      anisotropicCouplingVarianceRowCurvature D s a e T z = _
    rw [show anisotropicCouplingVarianceRowCurvature D s a e T z =
      anisotropicIncidentCurvature D s a e T (finiteCascadeGaussianRowPhysicalRecords
        (anisotropicCouplingFeature e) (trimRoot T) z) from
        finiteCascadeTreeGaussianRowCurvature_physical _ _ _ _ _ _ z]
    simp only [anisotropicCouplingRowObservable,finiteCascadeGaussianRowPhysicalRecords,
      spins_finiteCascadeShiftRecords]

theorem integral_anisotropicCouplingRowLaw_curvature (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (ha : a ≤ s.m 1)
    (e : AnisotropicCouplingIndex n) (T : FiniteTerminalGenealogy (k+2)) :
    (∫z,anisotropicCouplingVarianceRowCurvature D s a e T z
      ∂anisotropicCouplingVarianceRowLaw D s a e T (D.coupling e^2)) =
      ∫z,anisotropicIncidentCurvature D s a e T z
        ∂anisotropicTrimmedRecordedTreeLaw D s a T := by
  simpa only [anisotropicCouplingRowObservable,one_mul] using
    integral_anisotropicCouplingRowLaw_curvature_mul D s a ha e T (fun _ => 1) measurable_const

theorem hasDerivAt_anisotropicTreeLaw_physical_coupling_variance (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (ha : a ≤ s.m 1) (hq : s.q 1 = 0)
    (e : AnisotropicCouplingIndex n) (T : FiniteTerminalGenealogy (k+2))
    (hv : 0 < D.coupling e^2)
    (F : FiniteCascadeGenealogy.Samples (Configuration n) (asGenealogy T) → ℝ)
    (hF : Measurable F) (C : ℝ) (hC : 0 ≤ C) (hFb : ∀z,|F z| ≤ C) :
    HasDerivAt (fun u => ∫σ,F σ ∂anisotropicFiniteTreeLaw
      (anisotropicReplaceCouplingVariance D e u) s a (asGenealogy T))
      ((1/2:ℝ) * ((∫z,anisotropicCouplingRowObservable T F z * anisotropicIncidentCurvature D s a e T z
          ∂anisotropicTrimmedRecordedTreeLaw D s a T) -
        (∫σ,F σ ∂anisotropicFiniteTreeLaw D s a (asGenealogy T)) *
        (∫z,anisotropicIncidentCurvature D s a e T z
          ∂anisotropicTrimmedRecordedTreeLaw D s a T))) (D.coupling e^2) := by
  have hd := hasDerivAt_anisotropicFiniteTreeLaw_coupling_variance D s a ha hq e T
    (D.coupling e^2) hv F hF C hC hFb
  rw [integral_anisotropicCouplingRowLaw_curvature_mul D s a ha e T F hF,
    integral_anisotropicCouplingRowLaw_curvature D s a ha e T] at hd
  have he := integral_anisotropicFiniteCouplingRowLaw_spins D s a ha hq e T F hF C hC hFb
  change (∫z,anisotropicCouplingRowObservable T F z.2
    ∂anisotropicCouplingVarianceRowLaw D s a e T (D.coupling e^2)) = _ at he
  rw [he] at hd
  exact hd

end QuantitativeFollowup
