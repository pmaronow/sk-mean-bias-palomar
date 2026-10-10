module
public import QuantitativeFollowup.SupportingNativeRestartFieldDerivativeNodeMean
public import QuantitativeFollowup.AnisotropicTailHessian

@[expose] public section

/-! The retained posterior second differential is the actual physical
field Hessian at the corresponding clamped node. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology ContDiff BigOperators
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets SpinGlass.AT
variable {n k : ℕ}
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128

theorem anisotropicEnergyMap_coordinateFeature (D : AnisotropicSpinModel n) (i : Fin n) :
    anisotropicEnergyMap D (anisotropicCoordinateDirection n i)=cavityCoordinateFeature i := by
  ext σ
  exact anisotropicTerminalLinear_coordinate D σ i

theorem anisotropicFiniteCascade_second_field (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) (P : AnisotropicParameter n) (w : Field n) (i : Fin n) :
    fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
      (anisotropicSchemeMass s)
      (fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)) j))
      (anisotropicEnergyMap D P) (anisotropicEnergyMap D (anisotropicFieldInjection n w))
      (cavityCoordinateFeature i)=
      fderiv ℝ (fderiv ℝ (anisotropicFinitePotential D s j)) P
        (anisotropicFieldInjection n w) (anisotropicCoordinateDirection n i) := by
  let F:=finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
    (anisotropicSchemeMass s) (fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)) j
  let B:=anisotropicEnergyMap D
  let u:=anisotropicCoordinateDirection n i
  let K:=cavityCoordinateFeature i
  have hsF:=(contDiff_finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
    (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s)
      (fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)) j).fderiv_right (m:=∞) (by simp)
  have hsU:=(contDiff_anisotropicFinitePotential D s j).fderiv_right (m:=∞) (by simp)
  let A : (AnisotropicParameter n→L[ℝ]ℝ)→L[ℝ]ℝ:=ContinuousLinearMap.apply ℝ ℝ u
  let C : (FiniteStateField (Configuration n)→L[ℝ]ℝ)→L[ℝ]ℝ:=ContinuousLinearMap.apply ℝ ℝ K
  have he : (fun Q=>fderiv ℝ (anisotropicFinitePotential D s j) Q u)=
      fun Q=>fderiv ℝ F (B Q) K := by
    funext Q
    have hd:=fderiv_comp Q ((contDiff_finiteStateGaussianTerminalCascade
      (fun _ : Configuration n=>0) (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s)
      (fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)) j).differentiable (by simp) (B Q)) B.differentiableAt
    change fderiv ℝ (F ∘ B) Q u=_
    rw [hd,B.fderiv,ContinuousLinearMap.comp_apply,anisotropicEnergyMap_coordinateFeature]
  have hL:=A.hasFDerivAt.comp P ((hsU.differentiable (by simp) P).hasFDerivAt)
  have hR:=C.hasFDerivAt.comp P (((hsF.differentiable (by simp) (B P)).hasFDerivAt).comp P B.hasFDerivAt)
  have hLe : fderiv ℝ (fun Q=>fderiv ℝ (anisotropicFinitePotential D s j) Q u) P=
      A.comp (fderiv ℝ (fderiv ℝ (anisotropicFinitePotential D s j)) P) := by
    simpa only [Function.comp_def,A,ContinuousLinearMap.apply_apply] using hL.fderiv
  have hRe : fderiv ℝ (fun Q=>fderiv ℝ F (B Q) K) P=
      C.comp ((fderiv ℝ (fderiv ℝ F) (B P)).comp B) := by
    simpa only [Function.comp_def,C,ContinuousLinearMap.apply_apply] using hR.fderiv
  rw [he,hRe] at hLe
  have hx:=congrArg (fun d : AnisotropicParameter n→L[ℝ]ℝ=>d (anisotropicFieldInjection n w)) hLe
  simpa only [ContinuousLinearMap.comp_apply,A,C,ContinuousLinearMap.apply_apply,B,F,u,K] using hx

theorem anisotropicFiniteCascade_second_restart_node (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (q : Paper.Overlap) (x w : Field n)
    (v : ℕ) (hv : v≤k+2) (i : Fin n) (sample : VectorDisorderBrownianSample n) :
    fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
      (anisotropicSchemeMass (vectorClampedScheme s q q.property))
      (fun l=>(anisotropicEnergyMap D).comp
        (anisotropicSchemeInput D (vectorClampedScheme s q q.property) l)) (k+2-v)))
      (historyExtended (anisotropicFiniteRestartEnergyHistory D s g q x sample) v)
      (anisotropicEnergyMap D (anisotropicFieldInjection n w)) (cavityCoordinateFeature i)=
      fderiv ℝ (fderiv ℝ (anisotropicFiniteTailPotential D s (max q (anisotropicSchemeNode s v hv))))
        (anisotropicFiniteRestartPhysicalParameter D s g q x (anisotropicRestartElapsed s q v) sample)
        (anisotropicFieldInjection n w) (anisotropicCoordinateDirection n i) := by
  have hindex : (Fin.ofNat (k+3) v).val=v := by
    change v%(k+3)=v
    exact Nat.mod_eq_of_lt (by omega)
  have hp : historyExtended (anisotropicFiniteRestartEnergyHistory D s g q x sample) v=
      anisotropicEnergyMap D (anisotropicFiniteRestartPhysicalParameter D s g q x
        (anisotropicRestartElapsed s q v) sample) := by
    simp only [historyExtended,anisotropicFiniteRestartEnergyHistory,
      anisotropicFiniteRestartPhysicalHistory,historySample,hindex]
  rw [hp,anisotropicFiniteCascade_second_field,anisotropicFiniteTailPotential_max_node]

end QuantitativeFollowup
