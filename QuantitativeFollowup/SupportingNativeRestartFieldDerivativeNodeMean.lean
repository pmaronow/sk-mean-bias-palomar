module
public import QuantitativeFollowup.SupportingNativeRestartFieldDerivativeRecordedScore
public import QuantitativeFollowup.AnisotropicVarianceRestartNodeSquare
public import QuantitativeFollowup.AnisotropicFieldDerivative

@[expose] public section

/-! Exact retained means at every clamped original node, including those
collapsed onto the restart level. No atom or strict-grid hypothesis is used. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology ContDiff BigOperators
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets SpinGlass.AT
variable {n k : ℕ}
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128

theorem anisotropicFiniteTailPotential_max_node (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (q : Paper.Overlap) (v : ℕ) (hv : v≤k+2) :
    anisotropicFiniteTailPotential D s (max q (anisotropicSchemeNode s v hv))=
      anisotropicFinitePotential D (vectorClampedScheme s q q.property) (k+2-v) := by
  rw [←anisotropicTailRecursion_eq_clamped D s q q.property (by omega)]
  by_cases hqv : (q:ℝ) ≤ s.q v
  · have hm : max q (anisotropicSchemeNode s v hv)=anisotropicSchemeNode s v hv :=
      max_eq_right hqv
    rw [hm,anisotropicFiniteTailPotential_node D s v hv]
    exact (anisotropicTailRecursion_prefix_of_le D s q (by omega)
      (by simpa only [show k+2-(k+2-v)=v by omega] using hqv)).symm
  · rw [max_eq_left (show anisotropicSchemeNode s v hv≤q from le_of_not_ge hqv)]
    exact anisotropicTailRecursion_constant_suffix D s q (k+2-v) (by omega)
      (by simpa only [show k+2-(k+2-v)=v by omega] using le_of_not_ge hqv)
      (by omega) le_rfl

theorem anisotropicFiniteCascade_first_field (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) (P : AnisotropicParameter n) (w : Field n) :
    fderiv ℝ (finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
      (anisotropicSchemeMass s)
      (fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)) j)
      (anisotropicEnergyMap D P) (anisotropicEnergyMap D (anisotropicFieldInjection n w))=
      inner ℝ (anisotropicMagnetization D s j P) w := by
  have hd:=fderiv_comp P
    ((contDiff_finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
      (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s)
      (fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)) j).differentiable (by simp) _) (anisotropicEnergyMap D).differentiableAt
  have he : fderiv ℝ (anisotropicFinitePotential D s j) P=
      (fderiv ℝ (finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
        (anisotropicSchemeMass s)
        (fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)) j)
        (anisotropicEnergyMap D P)).comp (anisotropicEnergyMap D) := by
    change fderiv ℝ (_ ∘ anisotropicEnergyMap D) P=_
    simpa only [ContinuousLinearMap.fderiv] using hd
  rw [←ContinuousLinearMap.comp_apply,←he,fderiv_anisotropicFinitePotential_field]

theorem cascadePosteriorRecordedMean_anisotropic_restart_node (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (q : Paper.Overlap) (x w : Field n)
    (v : ℕ) (hv : v≤k+2) (sample : VectorDisorderBrownianSample n) :
    cascadePosteriorRecordedMean (fun _ : Configuration n=>0)
      (anisotropicSchemeMass (vectorClampedScheme s q q.property))
      (fun l=>(anisotropicEnergyMap D).comp
        (anisotropicSchemeInput D (vectorClampedScheme s q q.property) l))
      (k+2) v (anisotropicEnergyMap D (anisotropicFieldInjection n w))
      (anisotropicFiniteRestartEnergyHistory D s g q x sample)=
      inner ℝ (anisotropicFiniteTailMagnetization D s (max q (anisotropicSchemeNode s v hv))
        (anisotropicFiniteRestartPhysicalParameter D s g q x (anisotropicRestartElapsed s q v) sample)) w := by
  have hindex : (Fin.ofNat (k+3) v).val=v := by
    change v%(k+3)=v
    exact Nat.mod_eq_of_lt (by omega)
  have hp : historyExtended (anisotropicFiniteRestartEnergyHistory D s g q x sample) v=
      anisotropicEnergyMap D (anisotropicFiniteRestartPhysicalParameter D s g q x
        (anisotropicRestartElapsed s q v) sample) := by
    simp only [historyExtended,anisotropicFiniteRestartEnergyHistory,
      anisotropicFiniteRestartPhysicalHistory,historySample,hindex]
  unfold cascadePosteriorRecordedMean
  rw [hp,anisotropicFiniteCascade_first_field]
  congr 1
  unfold anisotropicFiniteTailMagnetization
  rw [anisotropicFiniteTailPotential_max_node D s q v hv]
  rfl

end QuantitativeFollowup
