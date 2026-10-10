module
public import FourPapersCommon.FiniteStatePosteriorCoordinateTowerIntegrability

@[expose] public section

/-! Actual normalized current-coordinate means are measurable in the parent
field. Their integrability is supplied by true Gaussian tilt integrability,
not by any desired posterior conditional identity. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal ContDiff NNReal
namespace FourPapersCommon
open SpinGlass.AT OverlapPaper
set_option maxHeartbeats 1200000
variable {S I : Type*} [Fintype S] [Fintype I] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S]

theorem integral_coordinateSpinLaw_feature_eq_inputMean (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (d : ℕ) (H K : FiniteStateField S) (g : FiniteStateGaussianInput I→ℝ) (hg : Measurable g)
    (hgi : Integrable g ((stdGaussian (FiniteStateGaussianInput I)).tilted
      (fun z=>a d*finiteStateGaussianTerminalCascade V a L d (H+L d z)))) :
    (∫z,g z.1*K z.2 ∂finiteStateGaussianCoordinateSpinLaw V a L d H)=
      ∫z,g z*fderiv ℝ (finiteStateGaussianTerminalCascade V a L d) (H+L d z) K
        ∂(stdGaussian (FiniteStateGaussianInput I)).tilted
          (fun z=>a d*finiteStateGaussianTerminalCascade V a L d (H+L d z)) := by
  let P:=(stdGaussian (FiniteStateGaussianInput I)).tilted
    (fun z=>a d*finiteStateGaussianTerminalCascade V a L d (H+L d z))
  let κ:=finiteStateGaussianCoordinateSpinKernel V a L d H
  haveI : IsMarkovKernel κ:=finiteStateGaussianCoordinateSpinKernel_markov V a ha L d H
  haveI : IsProbabilityMeasure P:=isProbabilityMeasure_tilted (integrable_exp_finiteStateGaussian_lipschitz
    _ (finiteStateGaussianTerminalCascade_lipschitz V a ha L d) (L d) H (a d))
  have hpres : MeasurePreserving Prod.fst (P ⊗ₘ κ) P:=⟨measurable_fst,Measure.fst_compProd P κ⟩
  have hb:=((hpres.integrable_comp_of_integrable hgi).norm).mul_const ‖K‖
  have hi : Integrable (fun z : FiniteStateGaussianInput I×S=>g z.1*K z.2)
      (finiteStateGaussianCoordinateSpinLaw V a L d H) := by
    apply hb.mono'
    · exact ((hg.comp measurable_fst).mul ((measurable_of_finite (fun σ:S=>K σ)).comp measurable_snd)).aestronglyMeasurable
    · exact .of_forall fun z=>by
        rw [Real.norm_eq_abs,abs_mul]
        exact mul_le_mul_of_nonneg_left
          (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le K z.2) (abs_nonneg _)
  rw [finiteStateGaussianCoordinateSpinLaw,Measure.integral_compProd hi]
  simp_rw [finiteStateGaussianCoordinateSpinKernel,Kernel.comap_apply,integral_const_mul,
    ←fderiv_finiteStateGaussianTerminalCascade_eq_gibbsMean V a ha L d]

theorem measurable_coordinateSpinLaw_feature_mean (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀i,0≤a i) (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (d : ℕ) (K : FiniteStateField S) (g : FiniteStateGaussianInput I→ℝ) (hg : Measurable g)
    (hgi : ∀H,Integrable g ((stdGaussian (FiniteStateGaussianInput I)).tilted
      (fun z=>a d*finiteStateGaussianTerminalCascade V a L d (H+L d z)))) :
    Measurable (fun H=>∫z,g z.1*K z.2 ∂finiteStateGaussianCoordinateSpinLaw V a L d H) := by
  have hm : Measurable (fun p : PosteriorCoordinateState S I=>
      g p.2*fderiv ℝ (finiteStateGaussianTerminalCascade V a L d) p.1 K) :=
    (hg.comp measurable_snd).mul
      ((((contDiff_one_finiteStateGaussianTerminalCascade V a ha L d).continuous_fderiv
        (by norm_num)).clm_apply continuous_const).measurable.comp measurable_fst)
  have hmean := hm.stronglyMeasurable.integral_kernel
    (κ:=posteriorCoordinateKernel V a L (d+1) 0)
  have he (H : FiniteStateField S) :
      (∫p,g p.2*fderiv ℝ (finiteStateGaussianTerminalCascade V a L d) p.1 K
        ∂posteriorCoordinateKernel V a L (d+1) 0 (H,0))=
      ∫z,g z.1*K z.2 ∂finiteStateGaussianCoordinateSpinLaw V a L d H := by
    rw [posteriorCoordinateKernel_apply V a ha L,
      integral_map (show Measurable (posteriorCoordinateUpdate L (d+1) 0 (H,0)) from
        (measurable_posteriorCoordinateUpdate L (d+1) 0).comp (measurable_const.prodMk measurable_id)).aemeasurable
        hm.aestronglyMeasurable]
    simp only [Nat.add_sub_cancel,Nat.sub_zero,posteriorCoordinateUpdate]
    exact (integral_coordinateSpinLaw_feature_eq_inputMean V a ha L d H K g hg (hgi H)).symm
  have he' := funext he
  rw [←he']
  exact hmean.measurable.comp (measurable_id.prodMk measurable_const)

end FourPapersCommon
