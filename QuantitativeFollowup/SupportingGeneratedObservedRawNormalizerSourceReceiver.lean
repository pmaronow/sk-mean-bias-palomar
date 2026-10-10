module
public import QuantitativeFollowup.SupportingGeneratedObservedRawNormalizerPairTransport
public import QuantitativeFollowup.FollowupCavityGeneratedRawForestHistoryStreamingKernel
public import FourPapersCommon.FinitePiLastProduct

@[expose] public section

/-! The sixth raw source is the terminal expectation of the genuinely
appended independent binary component. The arbitrary old joint terminal
observable is retained throughout the finite product split. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n m : ℕ}

def cavityGeneratedObservedRawNormalizerSourceExpectation
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m)
    (F : CavityGeneratedHistory Paper.Overlap m →
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (H : CavityGeneratedHistory Paper.Overlap (m+1)) : ℝ :=
  ∫σ, cavityGeneratedObservedRawNormalizerPairSourceTest W F H σ
    ∂(cavityGeneratedNativeForestTerminalProbability D μ a
      (cavityGeneratedObservedRawNormalizerForest W).depth
      (cavityGeneratedObservedRawNormalizerForest W).tree
      ((cavityGeneratedObservedRawNormalizerForest W).clock H) : Measure _)

private theorem old_coordinate_integral
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m)
    (F : CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (H : CavityGeneratedHistory Paper.Overlap (m+1)) :
    (∫τ, F (fun c => cavityGeneratedObservedRawComponentTerminalCastEquiv (n:=n) _ _
      (cavityGeneratedObservedRawNormalizerForest_old_component W c) (τ c))
      ∂Measure.pi (fun c : Fin W.componentCount =>
        cavityGeneratedObservedRawComponentTerminalMeasure D μ a
          ((cavityGeneratedObservedRawNormalizerForest W).component c.castSucc) H)) =
    ∫σ, F σ ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
      (W.clock (H ∘ Fin.castSucc)) : Measure _) := by
  let e (c : Fin W.componentCount) :=
    cavityGeneratedObservedRawComponentTerminalCastEquiv (n:=n) _ _
      (cavityGeneratedObservedRawNormalizerForest_old_component W c)
  let A := fun c : Fin W.componentCount =>
    cavityGeneratedObservedRawComponentTerminalMeasure D μ a
      ((cavityGeneratedObservedRawNormalizerForest W).component c.castSucc) H
  let B := fun c : Fin W.componentCount =>
    cavityGeneratedObservedRawComponentTerminalMeasure D μ a (W.component c) (H ∘ Fin.castSucc)
  have he (c : Fin W.componentCount) : MeasurePreserving (e c) (A c) (B c) :=
    cavityGeneratedObservedRawComponentTerminalCastEquiv_measurePreserving D μ a _ _ _ H
  have hp : MeasurePreserving (MeasurableEquiv.piCongrRight e) (Measure.pi A) (Measure.pi B) :=
    measurePreserving_pi A B he
  rw [cavityGeneratedObservedRawNativeForestTerminalMeasure_eq_components]
  exact hp.integral_comp' F

private theorem binary_coordinate_integral
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (H : CavityGeneratedHistory Paper.Overlap (m+1)) :
    (∫τ, nativeStreamingNormalizerBinaryTerminalTest n (H (Fin.last m)) τ
      ∂cavityGeneratedObservedRawComponentTerminalMeasure D μ a
        (cavityGeneratedObservedRawNormalizerComponent (m:=m)) H) =
      nativeStreamingFreshDefectMoment D μ a (H (Fin.last m)) := by
  change (∫τ, nativeStreamingNormalizerBinaryTerminalTest n (H (Fin.last m)) τ
    ∂(anisotropicRecordedProfileTreeLaw D μ a
      ((cavityGeneratedObservedRawNormalizerComponent (m:=m)).clock H)
      anisotropicBinaryObservationTree).map
      (fun z => finiteCascadeRecordTerminalSpins anisotropicBinaryObservationTree z.2)) = _
  rw [cavityGeneratedObservedRawNormalizerComponent_clock]
  have hi := integral_map_of_stronglyMeasurable
    (μ:=anisotropicRecordedProfileTreeLaw D μ a
      (anisotropicBinaryObservationSchedule (H (Fin.last m))) anisotropicBinaryObservationTree)
    ((measurable_finiteCascadeRecordTerminalSpins anisotropicBinaryObservationTree).comp measurable_snd)
    (measurable_of_finite (nativeStreamingNormalizerBinaryTerminalTest n (H (Fin.last m)))).stronglyMeasurable
  exact hi.trans (nativeStreamingNormalizer_binary_eq_freshDefectMoment D μ a (H (Fin.last m)))

theorem cavityGeneratedObservedRawNormalizerSourceExpectation_eq
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m)
    (F : CavityGeneratedHistory Paper.Overlap m →
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (H : CavityGeneratedHistory Paper.Overlap (m+1)) :
    cavityGeneratedObservedRawNormalizerSourceExpectation D μ a W F H =
      (∫σ, F (H ∘ Fin.castSucc) σ
        ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
          (W.clock (H ∘ Fin.castSucc)) : Measure _)) *
      nativeStreamingFreshDefectMoment D μ a (H (Fin.last m)) := by
  let V := cavityGeneratedObservedRawNormalizerForest W
  let A := fun i : Fin (W.componentCount+1) =>
    cavityGeneratedObservedRawComponentTerminalMeasure D μ a (V.component i) H
  let f : ((c : Fin W.componentCount) →
      CavityGeneratedObservedRawComponentTerminal n (V.component c.castSucc)) → ℝ :=
    fun τ => F (H ∘ Fin.castSucc) (fun c =>
      cavityGeneratedObservedRawComponentTerminalCastEquiv (n:=n) _ _
        (cavityGeneratedObservedRawNormalizerForest_old_component W c) (τ c))
  let g : CavityGeneratedObservedRawComponentTerminal n (V.component (Fin.last W.componentCount)) → ℝ :=
    fun τ => nativeStreamingNormalizerBinaryTerminalTest n (H (Fin.last m))
      (cavityGeneratedObservedRawComponentTerminalCastEquiv (n:=n) _ _
        (cavityGeneratedObservedRawNormalizerForest_new_component W) τ)
  have hsplit := integral_pi_coordinate_product A (Fin.last W.componentCount)
  rw [Fin.succAbove_last] at hsplit
  specialize hsplit f g
  have hf := old_coordinate_integral D μ a W (F (H ∘ Fin.castSucc)) H
  have hg : (∫τ, g τ ∂A (Fin.last W.componentCount)) =
      nativeStreamingFreshDefectMoment D μ a (H (Fin.last m)) := by
    have hp := cavityGeneratedObservedRawComponentTerminalCastEquiv_measurePreserving D μ a
      (V.component (Fin.last W.componentCount))
      cavityGeneratedObservedRawNormalizerComponent
      (cavityGeneratedObservedRawNormalizerForest_new_component W) H
    exact (hp.integral_comp' (nativeStreamingNormalizerBinaryTerminalTest n (H (Fin.last m)))).trans
      (binary_coordinate_integral D μ a H)
  calc
    _ = ∫σ, f (fun c => σ c.castSucc) * g (σ (Fin.last W.componentCount)) ∂Measure.pi A := by
      unfold cavityGeneratedObservedRawNormalizerSourceExpectation
      rw [cavityGeneratedObservedRawNativeForestTerminalMeasure_eq_components]
      apply integral_congr_ae
      refine .of_forall fun σ => ?_
      unfold cavityGeneratedObservedRawNormalizerPairSourceTest
      rw [cavityGeneratedObservedRawNormalizerFreshPair_defect]
      rfl
    _ = _ := by rw [hsplit,hf,hg]

theorem cavityGeneratedObservedRawNormalizerSourceExpectation_snoc
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m)
    (F : CavityGeneratedHistory Paper.Overlap m →
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap) :
    cavityGeneratedObservedRawNormalizerSourceExpectation D μ a W F (Fin.snoc h r) =
      (∫σ, F h σ ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
        (W.clock h) : Measure _)) * nativeStreamingFreshDefectMoment D μ a r := by
  have he : Fin.snoc h r ∘ Fin.castSucc = h := by
    funext i
    simp only [Function.comp_apply,Fin.snoc_castSucc]
  rw [cavityGeneratedObservedRawNormalizerSourceExpectation_eq,he,Fin.snoc_last]

theorem measurable_cavityGeneratedObservedRawNormalizerSourceExpectation
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m)
    (F : CavityGeneratedHistory Paper.Overlap m →
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (hF : Measurable (Function.uncurry F)) :
    Measurable (cavityGeneratedObservedRawNormalizerSourceExpectation D μ a W F) := by
  have hpre : Measurable (fun H : CavityGeneratedHistory Paper.Overlap (m+1) =>
      H ∘ Fin.castSucc) := Measurable.of_eval fun i => measurable_pi_apply i.castSucc
  have hold : Measurable (fun h : CavityGeneratedHistory Paper.Overlap m =>
      ∫σ, F h σ ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
        (W.clock h) : Measure _)) := by
    have hh := hF.stronglyMeasurable.integral_kernel_prod_right'
      (κ:=cavityGeneratedRawForestTerminalKernel D μ a W.depth W.tree W.clock
        W.measurable_clock W.clock_antitone)
    simpa only [Function.uncurry_apply_pair,cavityGeneratedRawForestTerminalKernel_apply] using hh.measurable
  have hlast : Measurable (fun H : CavityGeneratedHistory Paper.Overlap (m+1) =>
      H (Fin.last m)) := measurable_pi_apply (Fin.last m)
  have hfresh := (continuous_nativeStreamingFreshDefectMoment D μ a).measurable.comp hlast
  rw [show cavityGeneratedObservedRawNormalizerSourceExpectation D μ a W F =
    (fun H => (∫σ, F (H ∘ Fin.castSucc) σ
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
        (W.clock (H ∘ Fin.castSucc)) : Measure _)) *
      nativeStreamingFreshDefectMoment D μ a (H (Fin.last m))) from
    funext (cavityGeneratedObservedRawNormalizerSourceExpectation_eq D μ a W F)]
  exact (hold.comp hpre).mul hfresh

theorem cavityGeneratedObservedRawNormalizerFamily_source_receiver
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ) (ha : 0≤a)
    (W : CavityGeneratedObservedRawForest m)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (F : CavityGeneratedHistory Paper.Overlap m →
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (hF : Measurable (Function.uncurry F)) :
    (∫H, cavityGeneratedObservedRawNormalizerSourceExpectation D μ a W F H
      ∂cavityGeneratedNormalizerFamilyMeasure a (parisiFreeMeasure μ a) M) =
      a * (∫z : CavityGeneratedHistory Paper.Overlap m × Paper.Overlap,
        (∫σ, F z.1 σ ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
          (W.clock z.1) : Measure _)) * nativeStreamingFreshDefectMoment D μ a z.2
        ∂M.prod (parisiFreeMeasure μ a)) := by
  rw [cavityGeneratedNormalizerFamilyMeasure_integral a ha _ M _
    (measurable_cavityGeneratedObservedRawNormalizerSourceExpectation D μ a W F hF)]
  congr 1
  exact integral_congr_ae (.of_forall fun z =>
    cavityGeneratedObservedRawNormalizerSourceExpectation_snoc D μ a W F z.1 z.2)

theorem cavityGeneratedObservedRawNormalizerFamily_source_receiver_independent
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ) (ha : 0≤a)
    (W : CavityGeneratedObservedRawForest m)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [SFinite M]
    (F : CavityGeneratedHistory Paper.Overlap m →
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (hF : Measurable (Function.uncurry F)) :
    (∫H, cavityGeneratedObservedRawNormalizerSourceExpectation D μ a W F H
      ∂cavityGeneratedNormalizerFamilyMeasure a (parisiFreeMeasure μ a) M) =
      ∫h, a * (∫σ, F h σ
        ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
          (W.clock h) : Measure _)) *
        (∫r, nativeStreamingFreshDefectMoment D μ a r ∂parisiFreeMeasure μ a) ∂M := by
  let f : CavityGeneratedHistory Paper.Overlap m → ℝ := fun h =>
    ∫σ, F h σ ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
      (W.clock h) : Measure _)
  have hp := integral_prod_mul (μ:=M) (ν:=parisiFreeMeasure μ a) f
    (nativeStreamingFreshDefectMoment D μ a)
  rw [cavityGeneratedObservedRawNormalizerFamily_source_receiver D μ a ha W M F hF]
  change a * (∫z : CavityGeneratedHistory Paper.Overlap m × Paper.Overlap,
    f z.1 * nativeStreamingFreshDefectMoment D μ a z.2 ∂M.prod (parisiFreeMeasure μ a)) =
    ∫h, a * f h * (∫r, nativeStreamingFreshDefectMoment D μ a r ∂parisiFreeMeasure μ a) ∂M
  rw [hp,integral_mul_const,integral_const_mul]
  ring

end QuantitativeFollowup
