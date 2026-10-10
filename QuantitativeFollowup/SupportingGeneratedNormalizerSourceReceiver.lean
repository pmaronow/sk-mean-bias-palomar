module
public import QuantitativeFollowup.FollowupCavityGeneratedNormalizerFamily
public import QuantitativeFollowup.FollowupCavityGeneratedForestJointLaw

@[expose] public section

/-! The concrete appended forest receives the independent normalizer
source. The old history and arbitrary joint terminal observable are
retained. Measurability follows from the actual terminal kernel and fresh
defect moment, rather than from an assumed receiver identity. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n m : ℕ}

def printedGeneratedNormalizerSourceExpectation
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m)
    (F : CavityGeneratedHistory Paper.Overlap m →
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (H : CavityGeneratedHistory Paper.Overlap (m+1)) : ℝ :=
  ∫z, F (H ∘ Fin.castSucc)
      (cavityGeneratedForestTerminalProjection W.depth W.tree
        (printedGeneratedNormalizerOldRecord W.depth W.tree
          (printedGeneratedAppendRecordToNative W z)))*
    nativeStreamingNormalizerBinaryTerminalTest n (H (Fin.last m))
      (finiteCascadeRecordTerminalSpins anisotropicBinaryObservationTree
        (printedGeneratedNormalizerNewRecord W.depth W.tree
          (printedGeneratedAppendRecordToNative W z)).2)
    ∂cavityGeneratedNativeForestLaw D μ a (printedGeneratedNormalizerAppendedForest W).depth
      (printedGeneratedNormalizerAppendedForest W).tree
      ((printedGeneratedNormalizerAppendedForest W).clockTemplate.clock H)

theorem printedGeneratedNormalizerSourceExpectation_snoc
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m)
    (F : CavityGeneratedHistory Paper.Overlap m →
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap) :
    printedGeneratedNormalizerSourceExpectation D μ a W F (Fin.snoc h r) =
      (∫σ,F h σ ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
        (W.clockTemplate.clock h) : Measure (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree)))*
      nativeStreamingFreshDefectMoment D μ a r := by
  have he : Fin.snoc h r ∘ Fin.castSucc = h := by
    funext i
    simp only [Function.comp_apply,Fin.snoc_castSucc]
  unfold printedGeneratedNormalizerSourceExpectation
  rw [he,Fin.snoc_last]
  exact (printedGeneratedNormalizerAppendedForest_terminal_expectation D μ a W h r F).trans
    (congrArg (fun t : ℝ => (∫σ,F h σ
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
        (W.clockTemplate.clock h) : Measure (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree)))*t)
      (nativeStreamingFreshDefectMoment_eq_fresh D μ a r).symm)

theorem printedGeneratedNormalizerSourceExpectation_eq
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m)
    (F : CavityGeneratedHistory Paper.Overlap m →
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (H : CavityGeneratedHistory Paper.Overlap (m+1)) :
    printedGeneratedNormalizerSourceExpectation D μ a W F H =
      (∫σ,F (H ∘ Fin.castSucc) σ
        ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
          (W.clockTemplate.clock (H ∘ Fin.castSucc)) :
            Measure (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree)))*
      nativeStreamingFreshDefectMoment D μ a (H (Fin.last m)) := by
  have he : Fin.snoc (H ∘ Fin.castSucc) (H (Fin.last m)) = H := by
    funext i
    cases i using Fin.lastCases with
    | last => simp only [Fin.snoc_last]
    | cast i => simp only [Fin.snoc_castSucc,Function.comp_apply]
  have hh := printedGeneratedNormalizerSourceExpectation_snoc D μ a W F
    (H ∘ Fin.castSucc) (H (Fin.last m))
  rw [he] at hh
  exact hh

theorem measurable_printedGeneratedNormalizerSourceExpectation
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m)
    (F : CavityGeneratedHistory Paper.Overlap m →
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (hF : Measurable (Function.uncurry F)) :
    Measurable (printedGeneratedNormalizerSourceExpectation D μ a W F) := by
  have hpre : Measurable (fun H : CavityGeneratedHistory Paper.Overlap (m+1) =>
      H ∘ Fin.castSucc) := Measurable.of_eval fun i => measurable_pi_apply i.castSucc
  have hold : Measurable (fun h : CavityGeneratedHistory Paper.Overlap m =>
      ∫σ,F h σ ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
        (W.clockTemplate.clock h) : Measure (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree))) := by
    have hh := hF.stronglyMeasurable.integral_kernel_prod_right'
      (κ:=cavityGeneratedForestTerminalKernel D μ a W)
    simpa only [Function.uncurry_apply_pair,cavityGeneratedForestTerminalKernel_apply] using hh.measurable
  have hlast : Measurable (fun H : CavityGeneratedHistory Paper.Overlap (m+1) =>
      H (Fin.last m)) := measurable_pi_apply (Fin.last m)
  have hfresh := (continuous_nativeStreamingFreshDefectMoment D μ a).measurable.comp hlast
  have he : printedGeneratedNormalizerSourceExpectation D μ a W F =
      (fun H => (∫σ,F (H ∘ Fin.castSucc) σ
        ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
          (W.clockTemplate.clock (H ∘ Fin.castSucc)) :
            Measure (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree)))*
        nativeStreamingFreshDefectMoment D μ a (H (Fin.last m))) :=
    funext (printedGeneratedNormalizerSourceExpectation_eq D μ a W F)
  rw [he]
  exact (hold.comp hpre).mul hfresh

theorem printedGeneratedNormalizerFamily_source_receiver
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ) (ha : 0≤a)
    (W : CavityGeneratedConstructedForest m)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (F : CavityGeneratedHistory Paper.Overlap m →
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (hF : Measurable (Function.uncurry F)) :
    (∫H,printedGeneratedNormalizerSourceExpectation D μ a W F H
      ∂cavityGeneratedNormalizerFamilyMeasure a (parisiFreeMeasure μ a) M) =
      a*(∫z : CavityGeneratedHistory Paper.Overlap m × Paper.Overlap,
        (∫σ,F z.1 σ ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
          (W.clockTemplate.clock z.1) : Measure (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree)))*
        nativeStreamingFreshDefectMoment D μ a z.2 ∂M.prod (parisiFreeMeasure μ a)) := by
  rw [cavityGeneratedNormalizerFamilyMeasure_integral a ha _ M _
    (measurable_printedGeneratedNormalizerSourceExpectation D μ a W F hF)]
  congr 1
  exact integral_congr_ae (.of_forall fun z =>
    printedGeneratedNormalizerSourceExpectation_snoc D μ a W F z.1 z.2)

theorem printedGeneratedNormalizerFamily_source_receiver_independent
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ) (ha : 0≤a)
    (W : CavityGeneratedConstructedForest m)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [SFinite M]
    (F : CavityGeneratedHistory Paper.Overlap m →
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (hF : Measurable (Function.uncurry F)) :
    (∫H,printedGeneratedNormalizerSourceExpectation D μ a W F H
      ∂cavityGeneratedNormalizerFamilyMeasure a (parisiFreeMeasure μ a) M) =
      ∫h,a*(∫σ,F h σ
        ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
          (W.clockTemplate.clock h) : Measure (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree)))*
        (∫r,nativeStreamingFreshDefectMoment D μ a r ∂parisiFreeMeasure μ a) ∂M := by
  let f : CavityGeneratedHistory Paper.Overlap m → ℝ := fun h =>
    ∫σ,F h σ ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
      (W.clockTemplate.clock h) : Measure (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree))
  have hp := integral_prod_mul (μ:=M) (ν:=parisiFreeMeasure μ a) f
    (nativeStreamingFreshDefectMoment D μ a)
  rw [printedGeneratedNormalizerFamily_source_receiver D μ a ha W M F hF]
  change a*(∫z : CavityGeneratedHistory Paper.Overlap m × Paper.Overlap,
    f z.1*nativeStreamingFreshDefectMoment D μ a z.2 ∂M.prod (parisiFreeMeasure μ a)) =
    ∫h,a*f h*(∫r,nativeStreamingFreshDefectMoment D μ a r ∂parisiFreeMeasure μ a) ∂M
  rw [hp,integral_mul_const,integral_const_mul]
  ring

end QuantitativeFollowup
