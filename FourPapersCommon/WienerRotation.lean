module
public import FRSB.WienerReflection
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Process.FiniteDimensionalLaws

@[expose] public section

/-! Rotation invariance of two actual continuous Brownian paths. The proof
uses finite-dimensional Brownian laws and the measurable structure generated
by continuous-path evaluations, without assuming Banach-valued Gaussianity. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper
open scoped Topology NNReal ENNReal
namespace FourPapersCommon
set_option maxHeartbeats 1200000

abbrev WienerPath := C(Paper.Overlap, ℝ)
abbrev WienerPathPair := WienerPath × WienerPath

def wienerPairEval (p : WienerPathPair) : Paper.Overlap → ℝ × ℝ :=
  fun t => (p.1 t,p.2 t)

def wienerPairJoin (p : WienerPathPair) : C(Paper.Overlap, ℝ × ℝ) :=
  p.1.prodMk p.2

def wienerPairSplit (p : C(Paper.Overlap, ℝ × ℝ)) : WienerPathPair :=
  (ContinuousMap.fst.comp p,ContinuousMap.snd.comp p)

theorem measurable_wienerPairEval : Measurable wienerPairEval := by
  apply Measurable.of_eval
  intro t
  exact ((ProbabilityTheory.ContinuousMap.measurable_iff_eval (fun p : WienerPath => p)).mp
    measurable_id t).comp measurable_fst |>.prodMk
      (((ProbabilityTheory.ContinuousMap.measurable_iff_eval (fun p : WienerPath => p)).mp
        measurable_id t).comp measurable_snd)

theorem measurable_wienerPairJoin : Measurable wienerPairJoin := by
  rw [ProbabilityTheory.ContinuousMap.measurable_iff_eval]
  intro t
  exact (measurable_pi_apply t).comp measurable_wienerPairEval

theorem measurable_wienerPairSplit : Measurable wienerPairSplit := by
  apply Measurable.prodMk
  · rw [ProbabilityTheory.ContinuousMap.measurable_iff_eval]
    intro t
    exact ((ProbabilityTheory.ContinuousMap.measurable_iff_eval
      (fun p : C(Paper.Overlap, ℝ × ℝ) => p)).mp measurable_id t).fst
  · rw [ProbabilityTheory.ContinuousMap.measurable_iff_eval]
    intro t
    exact ((ProbabilityTheory.ContinuousMap.measurable_iff_eval
      (fun p : C(Paper.Overlap, ℝ × ℝ) => p)).mp measurable_id t).snd

theorem wienerPairMeasure_ext (P Q : Measure WienerPathPair)
    (h : P.map wienerPairEval=Q.map wienerPairEval) : P=Q := by
  have hj : P.map wienerPairJoin=Q.map wienerPairJoin := by
    have hm : (inferInstance : MeasurableSpace C(Paper.Overlap, ℝ × ℝ)) =
        MeasurableSpace.pi.comap (fun p : C(Paper.Overlap, ℝ × ℝ) => fun t => p t) := by
      calc
        _ = ⨆ t : Paper.Overlap, (inferInstance : MeasurableSpace (ℝ × ℝ)).comap
          (fun p : C(Paper.Overlap, ℝ × ℝ) => p t) :=
            ProbabilityTheory.ContinuousMap.measurableSpace_eq_iSup_comap_eval
        _ = _ := by simp only [MeasurableSpace.pi,MeasurableSpace.comap_iSup,
            MeasurableSpace.comap_comp,Function.comp_def]
    apply Measure.ext
    intro S hS
    change @MeasurableSet C(Paper.Overlap, ℝ × ℝ)
      (inferInstance : MeasurableSpace C(Paper.Overlap, ℝ × ℝ)) S at hS
    rw [hm] at hS
    rcases hS with ⟨T,hT,rfl⟩
    have hcoe : Measurable (fun p : C(Paper.Overlap, ℝ × ℝ) => fun t => p t) :=
      Measurable.of_eval fun t =>
        ((ProbabilityTheory.ContinuousMap.measurable_iff_eval
          (fun p : C(Paper.Overlap, ℝ × ℝ) => p)).mp measurable_id t)
    rw [← Measure.map_apply hcoe hT,←Measure.map_apply hcoe hT,
      Measure.map_map hcoe measurable_wienerPairJoin,
      Measure.map_map hcoe measurable_wienerPairJoin]
    exact congrArg (fun M => M T) h
  have hb := congrArg (fun M => M.map wienerPairSplit) hj
  rw [Measure.map_map measurable_wienerPairSplit measurable_wienerPairJoin,
    Measure.map_map measurable_wienerPairSplit measurable_wienerPairJoin] at hb
  have he : wienerPairSplit ∘ wienerPairJoin=id := by
    funext p
    rfl
  simpa only [he,Measure.map_id] using hb

theorem measurable_wiener_finite_evaluations (I : Finset Paper.Overlap) :
    Measurable (fun p : WienerPath => I.restrict (fun t => p t)) :=
  (Finset.measurable_restrict I).comp FRSB.measurable_continuousPath_coe

/-- Every finite vector of evaluations under the actual continuous path law
has the genuine centered Gaussian Brownian law. -/
theorem isGaussian_wiener_finite_evaluations (I : Finset Paper.Overlap) :
    IsGaussian (canonicalWienerMeasure.map (fun p : WienerPath => I.restrict (fun t => p t))) := by
  have hG := (isBrownianReal_canonicalBrownian.toIsPreBrownianReal.isGaussianProcess.comp_right
    (fun t : Paper.Overlap => t.1.toNNReal)).hasGaussianLaw I
  rw [canonicalWienerMeasure,Measure.map_map (measurable_wiener_finite_evaluations I)
    measurable_canonicalBrownianPath]
  exact hG.isGaussian_map

theorem integral_wiener_finite_evaluations (I : Finset Paper.Overlap) :
    (∫f,f ∂(canonicalWienerMeasure.map (fun p : WienerPath => I.restrict (fun t => p t))))=0 := by
  let ν := canonicalWienerMeasure.map (fun p : WienerPath => I.restrict (fun t => p t))
  have : IsGaussian ν := isGaussian_wiener_finite_evaluations I
  ext t
  rw [eval_integral]
  · change (∫f,f t ∂ν)=0
    have he : ν=canonicalBrownianMeasure.map
        (fun sample => I.restrict (fun t => canonicalBrownian t.1.toNNReal sample)) := by
      dsimp only [ν]
      rw [canonicalWienerMeasure,Measure.map_map (measurable_wiener_finite_evaluations I)
        measurable_canonicalBrownianPath]
      rfl
    rw [he]
    have hm : Measurable (fun sample => I.restrict
        (fun t : Paper.Overlap => canonicalBrownian t.1.toNNReal sample)) :=
      (Finset.measurable_restrict I).comp (Measurable.of_eval fun t =>
        measurable_canonicalBrownian t.1.toNNReal)
    rw [integral_map hm.aemeasurable (measurable_pi_apply t).aestronglyMeasurable]
    exact isBrownianReal_canonicalBrownian.toIsPreBrownianReal.integral_eval _
  · intro i
    exact (IsGaussian.integrable_id (μ:=ν)).eval i

/-- The actual product of two continuous Wiener paths is invariant under
any orthogonal planar rotation. This is proved from finite Brownian laws. -/
theorem canonicalWienerMeasure_rotation (θ : ℝ) :
    (canonicalWienerMeasure.prod canonicalWienerMeasure).map
      (ContinuousLinearMap.rotation θ : WienerPathPair →L[ℝ] WienerPathPair) =
      canonicalWienerMeasure.prod canonicalWienerMeasure := by
  have : IsProbabilityMeasure canonicalWienerMeasure := ⟨by
    rw [canonicalWienerMeasure,Measure.map_apply measurable_canonicalBrownianPath MeasurableSet.univ]
    simp⟩
  let P := canonicalWienerMeasure.prod canonicalWienerMeasure
  let R : WienerPathPair →L[ℝ] WienerPathPair := ContinuousLinearMap.rotation θ
  apply wienerPairMeasure_ext
  rw [Measure.map_map measurable_wienerPairEval R.measurable]
  have hmR : Measurable (fun p : WienerPathPair => wienerPairEval (R p)) :=
    measurable_wienerPairEval.comp R.measurable
  apply (map_eq_iff_forall_finset_map_restrict_eq hmR.aemeasurable
    measurable_wienerPairEval.aemeasurable).mpr
  intro I
  let r : WienerPath → (I → ℝ) := fun p => I.restrict (fun t => p t)
  let ν := canonicalWienerMeasure.map r
  let Rp : WienerPathPair → (I → ℝ) × (I → ℝ) := Prod.map r r
  let Rf : (I → ℝ) × (I → ℝ) →L[ℝ] (I → ℝ) × (I → ℝ) := ContinuousLinearMap.rotation θ
  let J : (I → ℝ) × (I → ℝ) → (I → ℝ × ℝ) := fun p t => (p.1 t,p.2 t)
  have hr : Measurable r := measurable_wiener_finite_evaluations I
  have hRp : Measurable Rp := hr.prodMap hr
  have hJ : Measurable J := Measurable.of_eval fun t =>
    ((measurable_pi_apply t).comp measurable_fst).prodMk
      ((measurable_pi_apply t).comp measurable_snd)
  have hp : P.map Rp=ν.prod ν := (Measure.map_prod_map _ _ hr hr).symm
  have : IsGaussian ν := isGaussian_wiener_finite_evaluations I
  have hz : (∫f,f ∂ν)=0 := integral_wiener_finite_evaluations I
  have hrot : (ν.prod ν).map Rf=ν.prod ν := IsGaussian.map_rotation_eq_self hz θ
  have heR : (fun p : WienerPathPair => I.restrict (wienerPairEval (R p))) =
      J ∘ Rf ∘ Rp := by
    funext p t
    simp only [J,Rf,Rp,R,wienerPairEval,r,Function.comp_def,
      ContinuousLinearMap.rotation_apply,Finset.restrict_def,Prod.map_fst,Prod.map_snd,
      ContinuousMap.add_apply,ContinuousMap.smul_apply,smul_eq_mul,Pi.add_apply,Pi.smul_apply]
  have he : (fun p : WienerPathPair => I.restrict (wienerPairEval p))=J ∘ Rp := rfl
  rw [heR,he]
  calc
    P.map (J ∘ Rf ∘ Rp) = ((P.map Rp).map Rf).map J := by
      rw [Measure.map_map hJ Rf.measurable,Measure.map_map (hJ.comp Rf.measurable) hRp]
      rfl
    _ = ((ν.prod ν).map Rf).map J := by rw [hp]
    _ = (ν.prod ν).map J := by rw [hrot]
    _ = P.map (J ∘ Rp) := by rw [←hp,Measure.map_map hJ hRp]

end FourPapersCommon
